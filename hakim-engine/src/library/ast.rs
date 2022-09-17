use serde::Serialize;

use crate::{
    engine::{Engine, Result},
    interactive::{suggest::Applicablity, SuggClass, SuggRule},
};

#[derive(Debug, Clone, Serialize)]
pub enum SuggTarget {
    Goal,
    Hyp,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct Signature {
    pub(crate) name: String,
    pub(crate) ty: String,
    pub(crate) hidden_args: usize,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) enum Sentence {
    Suggestion {
        target: SuggTarget,
        tactic: String,
        applicablity: Applicablity,
        class: SuggClass,
    },
    Import {
        name: String,
    },
    Axiom(Signature),
    Todo(Signature),
    Definition {
        name: String,
        body: String,
        hidden_args: usize,
    },
    Theorem {
        #[serde(flatten)]
        sig: Signature,
        proof: Vec<String>,
    },
}

fn eat_signature(mut r: &str) -> Signature {
    let hidden_args = eat_hidden_args(&mut r);
    if let Some((name, body)) = r.split_once(':') {
        return Signature {
            name: name.trim().to_string(),
            ty: body.to_string(),
            hidden_args,
        };
    }
    panic!("invalid signature {:?}", r);
}

fn eat_hidden_args(r: &mut &str) -> usize {
    let hidden_args = if let Some(x) = r.strip_prefix("#1 ") {
        *r = x;
        1
    } else if let Some(x) = r.strip_prefix("#2 ") {
        *r = x;
        2
    } else {
        0
    };
    hidden_args
}

impl Sentence {
    fn parse<'a, T: Iterator<Item = &'a str> + 'a>(it: &mut T) -> Self {
        let s = it.next().unwrap();
        if let Some(mut r) = s.strip_prefix("Suggest ") {
            let target = if let Some(x) = r.strip_prefix("goal ") {
                r = x;
                SuggTarget::Goal
            } else if let Some(x) = r.strip_prefix("hyp ") {
                r = x;
                SuggTarget::Hyp
            } else {
                panic!("invalid type for suggestion");
            };
            let applicablity = if let Some(x) = r.strip_prefix("default ") {
                r = x;
                Applicablity::Default
            } else if let Some(x) = r.strip_prefix("auto ") {
                r = x;
                Applicablity::Auto
            } else {
                Applicablity::Normal
            };
            let tactic = match r.split_once(';') {
                Some((t, rest)) => {
                    r = rest;
                    t.to_string()
                }
                None => panic!("missing semicolon in suggestion"),
            };
            let class = match r.split_once("=>") {
                Some((l, r)) => SuggClass::Pattern(l.trim().to_string(), r.trim().to_string()),
                None => match r.trim() {
                    "Destruct" => SuggClass::Destruct,
                    "Contradiction" => SuggClass::Contradiction,
                    "Rewrite" => SuggClass::Rewrite,
                    "intros" => SuggClass::Intros,
                    "Instantiate" => SuggClass::Instantiate,
                    "Trivial" => SuggClass::Trivial,
                    _ => panic!("unknown sugg class {r}"),
                },
            };
            return Sentence::Suggestion {
                target,
                tactic,
                applicablity,
                class,
            };
        }
        if let Some(r) = s.strip_prefix("Definition ") {
            if let Some((mut name, body)) = r.split_once(":=") {
                let hidden_args = eat_hidden_args(&mut name);
                return Sentence::Definition {
                    name: name.trim().to_string(),
                    body: body.to_string(),
                    hidden_args,
                };
            }
        }
        if let Some(r) = s.strip_prefix("Todo ") {
            return Sentence::Todo(eat_signature(r));
        }
        if let Some(r) = s.strip_prefix("Axiom ") {
            return Sentence::Axiom(eat_signature(r));
        }
        if let Some(r) = s.strip_prefix("Import ") {
            return Sentence::Import {
                name: r.to_string(),
            };
        }
        if let Some(r) = s.strip_prefix("Theorem ") {
            let mut proof = vec![];
            assert_eq!("Proof", it.next().unwrap());
            for x in it {
                if x == "Qed" {
                    break;
                }
                proof.push(x.to_string());
            }
            return Sentence::Theorem {
                sig: eat_signature(r),
                proof,
            };
        }
        panic!("invalid sentence {:?}", s);
    }

    pub(crate) fn add_to_engine(&self, engine: &mut Engine) -> Result<()> {
        match self.clone() {
            Sentence::Suggestion {
                target,
                tactic,
                applicablity,
                class,
            } => {
                let sugg = SuggRule {
                    class,
                    tactic,
                    applicablity,
                };
                match target {
                    SuggTarget::Hyp => engine.add_hyp_sugg(sugg),
                    SuggTarget::Goal => engine.add_goal_sugg(sugg),
                }
            }
            Sentence::Import { name } => engine.load_library(&name)?,
            Sentence::Todo(sig) | Sentence::Axiom(sig) | Sentence::Theorem { sig, .. } => {
                engine.add_axiom(&sig.name, &sig.ty, sig.hidden_args)?
            }
            Sentence::Definition {
                name,
                body,
                hidden_args,
            } => engine.add_definition(&name, &body, hidden_args)?,
        }
        Ok(())
    }

    pub(crate) fn name(&self) -> Option<&str> {
        match self {
            Sentence::Import { name } => Some(name),
            Sentence::Todo(sig) | Sentence::Axiom(sig) | Sentence::Theorem { sig, .. } => {
                Some(&sig.name)
            }
            _ => None,
        }
    }

    pub(crate) fn ty(&self) -> Option<&str> {
        match self {
            Sentence::Suggestion { .. } | Sentence::Import { .. } | Sentence::Definition { .. } => {
                None
            }
            Sentence::Todo(sig) | Sentence::Axiom(sig) | Sentence::Theorem { sig, .. } => {
                Some(&sig.ty)
            }
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct File(pub(crate) Vec<Sentence>);

fn split_by_sentence(text: &str) -> impl Iterator<Item = &str> {
    text.split('.').map(|x| x.trim()).filter(|x| !x.is_empty())
}

impl File {
    pub fn parse(text: &str) -> Self {
        let mut it = split_by_sentence(text).peekable();
        let mut r = vec![];
        while it.peek().is_some() {
            r.push(Sentence::parse(&mut it));
        }
        Self(r)
    }

    pub fn add_to_engine(&self, engine: &mut Engine) -> Result<()> {
        for x in self.0.iter() {
            x.add_to_engine(engine)?;
        }
        Ok(())
    }
}
