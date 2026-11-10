//! Thread quality-of-service placement for critical-path compile units.
//!
//! The in-process scheduler orders ready work by critical-path priority, but
//! on heterogeneous CPUs (Apple silicon: performance + efficiency cores) the
//! OS decides which core class a worker thread lands on, and it does so from
//! the thread's QoS class, not from anything the scheduler knows. A
//! critical-chain module that is scheduled onto an efficiency core runs
//! roughly 2x slower than it would on a performance core and stretches the
//! whole build.
//!
//! This module lets the scheduler raise the QoS of the worker thread for the
//! duration of one critical unit (and optionally lower it for background
//! units), with at most one critical unit per performance core in flight. On
//! platforms without a QoS API it is a no-op.

use std::sync::OnceLock;

/// How many critical units may be elevated at once. `0` disables placement.
///
/// Off by default: on the Tella clean build the elevated chain head
/// (`Layout__Types`) typechecks in 0.70 s instead of 1.46 s under a 12-worker
/// load, but wall time does not improve because the build is still
/// throughput-bound rather than chain-bound, and the elevated threads cost
/// the other workers a little. Enable with `RESCRIPT_CRITICAL_QOS=1` (one
/// slot per performance core) or `RESCRIPT_CRITICAL_QOS=<n>` once serial work
/// has shrunk enough for the critical chain to bound the build.
pub fn critical_slots() -> usize {
    static SLOTS: OnceLock<usize> = OnceLock::new();
    *SLOTS.get_or_init(|| {
        if !placement_supported() {
            return 0;
        }
        match std::env::var("RESCRIPT_CRITICAL_QOS").ok().as_deref() {
            Some("1") | Some("on") | Some("true") | Some("yes") => performance_core_count(),
            Some(value) => value.parse::<usize>().unwrap_or(0),
            None => 0,
        }
    })
}

/// Whether non-critical units should be demoted below the default class so
/// the OS prefers efficiency cores for them. Off unless
/// `RESCRIPT_BACKGROUND_QOS=1`.
pub fn demote_background() -> bool {
    static DEMOTE: OnceLock<bool> = OnceLock::new();
    *DEMOTE.get_or_init(|| placement_supported() && env_flag_on("RESCRIPT_BACKGROUND_QOS"))
}

fn env_flag_on(name: &str) -> bool {
    matches!(
        std::env::var(name).as_deref(),
        Ok("1") | Ok("on") | Ok("true") | Ok("yes")
    )
}

/// Placement class for one scheduled unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnitClass {
    /// Highest-priority ready work; prefer performance cores.
    Critical,
    /// Everything else; leave the thread at its default class.
    Default,
    /// Work that can run behind everything else; prefer efficiency cores.
    Background,
}

/// RAII guard that applies a placement class to the current thread and
/// restores the default class when the unit finishes.
pub struct UnitPlacementGuard {
    applied: bool,
}

impl UnitPlacementGuard {
    pub fn enter(class: UnitClass) -> Self {
        let applied = match class {
            UnitClass::Critical => set_thread_class(ThreadClass::UserInitiated),
            UnitClass::Background => demote_background() && set_thread_class(ThreadClass::Utility),
            UnitClass::Default => false,
        };
        Self { applied }
    }
}

impl Drop for UnitPlacementGuard {
    fn drop(&mut self) {
        if self.applied {
            set_thread_class(ThreadClass::Default);
        }
    }
}

#[derive(Clone, Copy)]
enum ThreadClass {
    UserInitiated,
    Default,
    Utility,
}

#[cfg(target_os = "macos")]
fn placement_supported() -> bool {
    true
}

#[cfg(not(target_os = "macos"))]
fn placement_supported() -> bool {
    false
}

#[cfg(target_os = "macos")]
fn set_thread_class(class: ThreadClass) -> bool {
    let qos = match class {
        ThreadClass::UserInitiated => libc::qos_class_t::QOS_CLASS_USER_INITIATED,
        ThreadClass::Default => libc::qos_class_t::QOS_CLASS_DEFAULT,
        ThreadClass::Utility => libc::qos_class_t::QOS_CLASS_UTILITY,
    };
    // SAFETY: `pthread_set_qos_class_self_np` only reads its two scalar
    // arguments and affects the calling thread's scheduling class.
    unsafe { libc::pthread_set_qos_class_self_np(qos, 0) == 0 }
}

#[cfg(not(target_os = "macos"))]
fn set_thread_class(_class: ThreadClass) -> bool {
    false
}

/// The value of the integer sysctl `name`, when the system has it.
#[cfg(target_os = "macos")]
fn sysctl_u32(name: &std::ffi::CStr) -> Option<u32> {
    let mut value: u32 = 0;
    let mut len = std::mem::size_of::<u32>();
    // SAFETY: `sysctlbyname` writes at most `len` bytes into `value`, and both
    // pointers stay valid for the duration of the call.
    let rc = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            (&mut value as *mut u32).cast(),
            &mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    (rc == 0).then_some(value)
}

/// Number of logical performance cores, or the logical core count when the
/// platform does not distinguish core classes.
#[cfg(target_os = "macos")]
fn performance_core_count() -> usize {
    match sysctl_u32(c"hw.perflevel0.logicalcpu") {
        Some(count) if count > 0 => count as usize,
        _ => num_cpus::get_physical().max(1),
    }
}

/// Number of logical efficiency cores; 0 when the CPU has one core class or
/// the platform does not report core classes.
#[cfg(target_os = "macos")]
pub fn efficiency_core_count() -> usize {
    sysctl_u32(c"hw.perflevel1.logicalcpu").unwrap_or(0) as usize
}

#[cfg(not(target_os = "macos"))]
pub fn efficiency_core_count() -> usize {
    0
}

#[cfg(not(target_os = "macos"))]
fn performance_core_count() -> usize {
    num_cpus::get_physical().max(1)
}
