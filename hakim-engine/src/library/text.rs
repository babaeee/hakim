use std::{collections::HashMap, path::PathBuf};

use lazy_static::lazy_static;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
#[cfg(target_arch = "wasm32")]
extern "C" {
    fn load_lib_json() -> JsValue;
}

#[cfg(target_arch = "wasm32")]
lazy_static! {
    static ref LIB_TEXT_STORE: HashMap<String, String> =
        serde_wasm_bindgen::from_value(load_lib_json()).unwrap();
}

#[cfg(not(target_arch = "wasm32"))]
lazy_static! {
    static ref LIB_TEXT_STORE: HashMap<String, String> = {
        let mut r = HashMap::default();
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.pop();
        d.push("library");
        let files = std::fs::read_dir(d).unwrap();
        for f in files {
            let f = f.unwrap().path();
            let name = f.file_name().unwrap().to_str().unwrap().to_string();
            if let Some(name) = name.strip_suffix(".v") {
                let text = std::fs::read_to_string(f).unwrap();
                r.insert(name.to_string(), text);
            }
        }
        r
    };
}

pub fn load_text(name: &str) -> Option<&str> {
    LIB_TEXT_STORE.get(name).map(|x| x.as_str())
}

#[cfg(test)]
pub fn all_names() -> impl Iterator<Item = &'static String> {
    LIB_TEXT_STORE.keys()
}
