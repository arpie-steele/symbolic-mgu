use symbolic_mgu::{get_formatter, Metavariable, SimpleType, WideMetavariable};
use SimpleType::*;

fn main() {
    // Create a wide variable with subscript: φ₁ (index 13 = second cycle of Boolean vars)
    let var = WideMetavariable::try_from_type_and_index(Boolean, 13).unwrap();

    println!("Testing subscripted variable: φ₁₃\n");

    // Test UTF-8 color formatter
    let utf8_color = get_formatter("utf8-color");
    println!("UTF-8 Color:");
    println!("{}", var.format_with(&*utf8_color));
    println!();

    // Test HTML color formatter
    let html_color = get_formatter("html-color");
    println!("HTML Color:");
    println!("{}", var.format_with(&*html_color));
    println!();

    // Test plain UTF-8
    let utf8 = get_formatter("utf8");
    println!("Plain UTF-8:");
    println!("{}", var.format_with(&*utf8));
    println!();

    // Test plain HTML
    let html = get_formatter("html");
    println!("Plain HTML:");
    println!("{}", var.format_with(&*html));
}
