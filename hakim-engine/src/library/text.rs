pub fn load_text(name: &str) -> Option<&str> {
    Some(match name {
        "Arith" => include_str!("Arith.v"),
        _ => return None,
    })
}
