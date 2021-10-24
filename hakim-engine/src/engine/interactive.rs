use std::collections::HashMap;

use im::vector;

use crate::brain::TermRef;

use super::{
    tactic::{self, add_hyp, apply, intros, rewrite, ring},
    Engine, Error,
};

#[derive(Debug, Clone)]
pub struct InteractiveFrame {
    pub goal: TermRef,
    pub hyps: HashMap<String, TermRef>,
    pub engine: Engine,
}

#[derive(Debug, Clone)]
pub struct InteractiveSnapshot {
    pub frames: im::Vector<InteractiveFrame>,
}

pub struct HistoryRecord {
    tactic: String,
    snapshot: InteractiveSnapshot,
}

pub struct InteractiveSession {
    history: Vec<HistoryRecord>,
}

fn smart_split(text: &str) -> Vec<String> {
    let mut r = vec![];
    let mut s = "".to_string();
    let mut d = 0;
    for c in text.chars() {
        if c == '(' {
            d += 1;
        }
        if c == ')' {
            d -= 1;
        }
        if d != 0 {
            s.push(c);
            continue;
        }
        if c.is_whitespace() {
            if !s.is_empty() {
                r.push(s);
                s = "".to_string();
            }
            continue;
        }
        s.push(c);
    }
    if !s.is_empty() {
        r.push(s);
    }
    r
}

impl InteractiveSession {
    pub fn new(engine: Engine, goal: &str) -> Result<Self, Error> {
        let snapshot = InteractiveSnapshot::new(engine, goal)?;
        let hr = HistoryRecord {
            snapshot,
            tactic: "Goal".to_string(),
        };
        Ok(InteractiveSession { history: vec![hr] })
    }

    pub fn last_snapshot(&self) -> &InteractiveSnapshot {
        &self.history.last().unwrap().snapshot
    }

    pub fn run_tactic(&mut self, line: &str) -> Result<(), tactic::Error> {
        if line.trim() == "Undo" {
            return self.undo();
        }
        let snapshot = self.last_snapshot().run_tactic(line)?;
        self.history.push(HistoryRecord {
            tactic: line.to_string(),
            snapshot,
        });
        Ok(())
    }

    pub fn monitor_string(&self) -> String {
        self.last_snapshot().monitor_string()
    }

    pub fn print(&self) {
        println!("{}", self.monitor_string());
    }

    pub fn is_finished(&self) -> bool {
        self.last_snapshot().is_finished()
    }

    pub fn undo(&mut self) -> Result<(), tactic::Error> {
        if self.history.len() <= 1 {
            return Err(tactic::Error::CanNotUndo);
        }
        self.history.pop();
        Ok(())
    }

    pub fn get_history(&self) -> Vec<String> {
        self.history.iter().map(|x| x.tactic.clone()).collect()
    }
}

impl InteractiveSnapshot {
    pub fn new(engine: Engine, goal: &str) -> Result<InteractiveSnapshot, Error> {
        let goal_term = engine.parse_text(goal)?;
        let frame = InteractiveFrame {
            hyps: Default::default(),
            goal: goal_term,
            engine,
        };
        Ok(InteractiveSnapshot {
            frames: vector![frame],
        })
    }

    pub fn monitor_string(&self) -> String {
        if self.is_finished() {
            return "No more subgoals.".to_string();
        }
        let goal_count = self.frames.len();
        let mut r = "".to_string();
        for (name, ty) in &self.frames.last().unwrap().hyps {
            r += &format!(" {}: {:#?}\n", name, ty);
        }
        for (i, frame) in self.frames.iter().rev().enumerate() {
            r += &format!(
                "--------------------------------------------({}/{})\n",
                i + 1,
                goal_count
            );
            r += &format!("    {:#?}\n", frame.goal);
        }
        r
    }

    pub fn run_tactic(&self, line: &str) -> Result<Self, tactic::Error> {
        let parts = smart_split(line);
        let mut parts = parts.into_iter();
        let name = parts.next().ok_or(tactic::Error::EmptyTactic)?;
        match name.as_str() {
            "intros" => intros(self, parts),
            "rewrite" => rewrite(self, parts),
            "apply" => apply(self, parts),
            "add_hyp" => add_hyp(self, parts),
            "ring" => ring(self),
            _ => Err(tactic::Error::UnknownTactic(name.to_string())),
        }
    }

    pub fn pop_frame(&mut self) -> InteractiveFrame {
        self.frames.pop_back().unwrap()
    }

    pub fn push_frame(&mut self, frame: InteractiveFrame) {
        self.frames.push_back(frame);
    }

    pub fn is_finished(&self) -> bool {
        self.frames.is_empty()
    }
}

impl InteractiveFrame {
    pub fn add_hyp_with_name(&mut self, name: &str, ty: TermRef) -> tactic::Result<()> {
        self.engine.add_axiom_with_term(name, ty.clone())?;
        self.hyps.insert(name.to_string(), ty);
        Ok(())
    }
}
