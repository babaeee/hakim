pub fn load_text(name: &str) -> Option<&str> {
    Some(match name {
        "Arith" => include_str!("Arith.v"),
        "Logic" => include_str!("Logic.v"),
        _ => return None,
    })
}
