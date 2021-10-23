use std::collections::HashMap;

use crate::brain::TermRef;

use super::{
    tactic::{self, apply, intros, rewrite, ring},
    Engine, Error,
};

#[derive(Debug, Clone)]
pub struct InteractiveFrame {
    pub goal: TermRef,
    pub hyps: HashMap<String, TermRef>,
}

#[derive(Debug, Clone)]
pub struct InteractiveSnapshot {
    pub frames: Vec<InteractiveFrame>,
    pub engine: Engine,
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
        };
        Ok(InteractiveSnapshot {
            engine,
            frames: vec![frame],
        })
    }

    pub fn monitor_string(&self) -> String {
        if self.is_finished() {
            return "No more subgoals.".to_string();
        }
        let mut r = "".to_string();
        for frame in &self.frames {
            for (name, ty) in &frame.hyps {
                r += &format!(" {}: {:#?}\n", name, ty);
            }
            r += &format!("--------------------------------------------\n");
            r += &format!("    {:#?}\n", frame.goal);
        }
        r
    }

    pub fn current_frame(&mut self) -> &mut InteractiveFrame {
        self.frames.last_mut().unwrap()
    }

    pub fn run_tactic(&self, line: &str) -> Result<Self, tactic::Error> {
        let parts = smart_split(line);
        let mut parts = parts.into_iter();
        let name = parts.next().ok_or(tactic::Error::EmptyTactic)?;
        match name.as_str() {
            "intros" => intros(self, parts),
            "rewrite" => rewrite(self, parts),
            "apply" => apply(self, parts),
            "ring" => ring(self),
            _ => Err(tactic::Error::UnknownTactic(name.to_string())),
        }
    }

    pub fn solve_goal(&mut self) {
        self.frames.pop();
    }

    pub fn add_hyp_with_name(&mut self, name: &str, ty: TermRef) -> tactic::Result<()> {
        self.engine.add_axiom_with_term(name, ty.clone())?;
        self.current_frame().hyps.insert(name.to_string(), ty);
        Ok(())
    }

    pub fn is_finished(&self) -> bool {
        self.frames.is_empty()
    }
}
