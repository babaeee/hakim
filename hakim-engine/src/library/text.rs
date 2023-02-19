use std::{collections::HashMap, sync::Mutex};

pub static LIB_TEXT_STORE: Mutex<Option<HashMap<String, String>>> = Mutex::new(None);

fn get_lib_text<K>(job: impl FnOnce(&HashMap<String, String>) -> K) -> K {
    let mut guard = LIB_TEXT_STORE.lock().unwrap();
    #[cfg(not(target_arch = "wasm32"))]
    if guard.is_none() {
        *guard = Some({
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
        })
    }
    job(guard.as_ref().unwrap())
}

pub fn load_text(name: &str) -> Option<String> {
    get_lib_text(|x| x.get(name).cloned())
}

pub fn all_names() -> impl Iterator<Item = String> {
    get_lib_text(|x| x.keys().cloned().collect::<Vec<_>>().into_iter())
}
