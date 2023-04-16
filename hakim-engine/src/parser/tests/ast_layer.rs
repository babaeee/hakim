//! Parsing and pretty printing without going through engine and brain. Add normal test if possible

use crate::parser::parse;

fn parse_not_pretty(text: &str, expected: &str) {
    let ast = parse(text).unwrap();
    let pretty = format!("{}", ast);
    assert_eq!(pretty, expected);
    let ast = parse(expected).unwrap();
    let pretty = format!("{}", ast);
    assert_eq!(pretty, expected);
}

#[test]
fn number_are_not_stored_in_ast_completely() {
    parse_not_pretty("1.0", "1.");
}
