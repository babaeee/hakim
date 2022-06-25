use serde::{Deserialize, Serialize};

use super::{smart_split, Session};

#[derive(Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum MouseTarget {
    Goal,
    NextGoal { index: usize },
    Hyp { name: String },
    Lib { name: String },
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum GraphicalAction {
    DblClick { target: MouseTarget },
    DragDrop { from: MouseTarget, to: MouseTarget },
    NewAssertion,
}

use GraphicalAction::*;
use MouseTarget::*;

pub fn action_of_tactic(session: &Session, tactic: &str) -> Option<GraphicalAction> {
    let frame = session.last_snapshot().last_frame();
    let parts = smart_split(tactic);
    let mut parts_iter = parts.iter().map(|x| x.as_str());
    let name = parts_iter.next()?;
    match name {
        "apply" => {
            if parts.len() == 2 {
                let lem = parts_iter.next()?;
                if frame.hyps.iter().any(|x| x.name == lem) {
                    return Some(DragDrop {
                        from: Hyp {
                            name: lem.to_string(),
                        },
                        to: Goal,
                    });
                }
            }
        }
        "add_hyp" => return Some(NewAssertion),
        _ => (),
    }
    None
}
