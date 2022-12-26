use std::collections::HashMap;

use lazy_static::lazy_static;

#[cfg(target_arch = "wasm32")]
thread_local! {
    pub static LIB_TEXT_STORE: std::cell::RefCell<HashMap<String,String>> = std::cell::RefCell::new(HashMap::new());
}

#[cfg(not(target_arch = "wasm32"))]
lazy_static! {
    static ref LIB_TEXT_STORE: HashMap<String, String> = {
        use std::path::PathBuf;
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
                r.insert(format!("/{name}"), text);
            } else {
                panic!("bad library name {name}. Libraries should end with `.v`");
            }
        }
        r
    };
}

#[cfg(not(target_arch = "wasm32"))]
fn get_lib_text<K>(job: impl FnOnce(&HashMap<String, String>) -> K) -> K {
    job(&LIB_TEXT_STORE)
}

#[cfg(target_arch = "wasm32")]
fn get_lib_text<K>(job: impl FnOnce(&HashMap<String, String>) -> K) -> K {
    LIB_TEXT_STORE.with(|x| job(&x.borrow()))
}

pub fn load_text(name: &str) -> Option<String> {
    get_lib_text(|x| x.get(name).cloned())
}

pub fn all_names() -> impl Iterator<Item = String> {
    get_lib_text(|x| x.keys().cloned().collect::<Vec<_>>().into_iter())
}
