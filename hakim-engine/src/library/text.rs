pub fn load_text(name: &str) -> Option<&str> {
    Some(match name {
        "All" => include_str!("All.v"),
        "Arith" => include_str!("Arith.v"),
        "Logic" => include_str!("Logic.v"),
        "Eq" => include_str!("Eq.v"),
        "NumberTheory" => include_str!("NumberTheory.v"),
        "ProductOperator" => include_str!("ProductOperator.v"),
        "Sigma" => include_str!("Sigma.v"),
        "Induction" => include_str!("Induction.v"),
        "Set" => include_str!("Set.v"),
        _ => return None,
    })
}
