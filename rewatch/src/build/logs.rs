use crate::build::packages::Package;
use crate::helpers;
use ahash::AHashMap;
use log::error;
use rayon::prelude::*;
use regex::Regex;
use std::borrow::Cow;
use std::fs::{self, File};
use std::io::prelude::*;
use std::path::PathBuf;
use std::sync::LazyLock;

use super::packages;

fn get_log_file_path(package: &packages::Package) -> PathBuf {
    package.get_build_path().join(".compiler.log")
}

static ANSI_ESCAPE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"[\u001b\u009b]\[[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-ORZcf-nqry=><]")
        .expect("Could not create regex")
});

pub(crate) fn escape_colours(str: &str) -> Cow<'_, str> {
    ANSI_ESCAPE.replace_all(str, "")
}

fn write_to_log_file(mut file: File, package_name: &str, content: &str) {
    if let Err(e) = file.write_all(escape_colours(content).as_bytes()) {
        error!(
            "Could not create compiler log file. {}. \n{:?}",
            &package_name, &e
        );
    }
}

pub fn initialize(packages: &AHashMap<String, Package>) {
    packages.par_iter().for_each(|(name, package)| {
        let log_path = get_log_file_path(package);
        if let Some(parent) = log_path.parent()
            && let Err(error) = fs::create_dir_all(parent)
        {
            error!("Cannot create compiler log directory for package {name}: {error}");
            return;
        }
        match File::create(&log_path) {
            Ok(file) => write_to_log_file(file, name, &format!("#Start({})\n", helpers::get_system_time())),
            Err(error) => error!(
                "Cannot create compiler log {} for package {name}: {error}",
                log_path.display()
            ),
        }
    })
}

pub fn append(package: &packages::Package, str: &str) {
    let log_path = get_log_file_path(package);
    if let Some(parent) = log_path.parent()
        && let Err(error) = fs::create_dir_all(parent)
    {
        error!(
            "Cannot create compiler log directory for package {}: {error}",
            package.name
        );
        return;
    }
    match File::options().append(true).create(true).open(&log_path) {
        Ok(file) => write_to_log_file(file, &package.name, str),
        Err(error) => error!("Cannot write compiler log {}: {error}", log_path.display()),
    }
}

pub fn finalize(packages: &AHashMap<String, Package>) {
    packages.par_iter().for_each(|(name, package)| {
        let _ = File::options()
            .append(true)
            .create(true)
            .open(get_log_file_path(package))
            .map(|file| write_to_log_file(file, name, &format!("#Done({})\n", helpers::get_system_time())));
    })
}
