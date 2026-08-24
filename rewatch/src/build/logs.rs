use crate::build::packages::Package;
use crate::helpers;
use ahash::AHashMap;
use log::error;
use rayon::prelude::*;
use regex::Regex;
use std::fs::{self, File};
use std::io::prelude::*;
use std::path::PathBuf;

use super::packages;

enum Location {
    Bs,
    Ocaml,
}

fn get_log_file_path(package: &packages::Package, subfolder: Location) -> PathBuf {
    let build_folder = match subfolder {
        Location::Bs => package.get_build_path(),
        Location::Ocaml => package.get_ocaml_build_path(),
    };

    build_folder.join(".compiler.log")
}

pub fn does_ocaml_build_compiler_log_exist(package: &packages::Package) -> bool {
    get_log_file_path(package, Location::Ocaml).exists()
}

fn escape_colours(str: &str) -> String {
    let re = Regex::new(r"[\u001b\u009b]\[[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-ORZcf-nqry=><]")
        .expect("Could not create regex");
    re.replace_all(str, "").to_string()
}

fn write_to_log_file(mut file: File, package_name: &str, content: &str) {
    let res = file.write(escape_colours(content).as_bytes()).map_err(|e| {
        error!(
            "Could not create compiler log file. {}. \n{:?}",
            &package_name, &e
        );
    });

    match res {
        Ok(_) => {}
        Err(e) => error!(
            "Could not create compiler log file. {}. \n{:?}",
            &package_name, &e
        ),
    }
}

pub fn initialize(packages: &AHashMap<String, Package>) {
    packages.par_iter().for_each(|(name, package)| {
        let log_path = get_log_file_path(package, Location::Bs);
        if let Some(parent) = log_path.parent()
            && let Err(error) = fs::create_dir_all(parent)
        {
            error!("Cannot create compiler log directory for package {name}: {error}");
            return;
        }
        match File::create(&log_path) {
            Ok(file) => write_to_log_file(file, name, &format!("#Start({})\n", helpers::get_system_time())),
            Err(error) => error!("Cannot create compiler log {} for package {name}: {error}", log_path.display()),
        }
    })
}

pub fn append(package: &packages::Package, str: &str) {
    let log_path = get_log_file_path(package, Location::Bs);
    if let Some(parent) = log_path.parent()
        && let Err(error) = fs::create_dir_all(parent)
    {
        error!("Cannot create compiler log directory for package {}: {error}", package.name);
        return;
    }
    match File::options().append(true).create(true).open(&log_path) {
        Ok(file) => write_to_log_file(file, &package.name, str),
        Err(error) => error!("Cannot write compiler log {}: {error}", log_path.display()),
    }
}

pub fn finalize(packages: &AHashMap<String, Package>) {
    packages.par_iter().for_each(|(name, package)| {
        let bs_log_path = get_log_file_path(package, Location::Bs);
        let ocaml_log_path = get_log_file_path(package, Location::Ocaml);
        let _ = File::options()
            .append(true)
            .create(true)
            .open(&bs_log_path)
            .map(|file| write_to_log_file(file, name, &format!("#Done({})\n", helpers::get_system_time())));

        if let Some(parent) = ocaml_log_path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        let _ = std::fs::copy(bs_log_path, ocaml_log_path);
    })
}
