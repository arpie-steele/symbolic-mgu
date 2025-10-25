//! Set flag if this is a nightly release

fn main() {
    // Tell cargo about the cfg we're using
    println!("cargo::rustc-check-cfg=cfg(nightly)");

    // Check if we're using nightly
    let is_nightly = version_check::is_feature_flaggable().unwrap_or(false);

    if is_nightly {
        println!("cargo:rustc-cfg=nightly");
    }
}
