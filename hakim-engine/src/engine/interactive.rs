use std::collections::HashMap;

use crate::brain::TermRef;

use super::{Engine, tactic::{self, apply, intros, rewrite}, Error};

pub struct InteractiveFrame {
    pub goal: TermRef,
    pub hyps: HashMap<String, TermRef>,
}

pub struct InteractiveSession<'a> {
    pub frames: Vec<InteractiveFrame>,
    pub engine: &'a mut Engine,
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
    r.push(s);
    r
}

impl InteractiveSession<'_> {
    pub fn new<'a>(engine: &'a mut Engine, goal: &str) -> Result<InteractiveSession<'a>, Error> {
        let goal_term = engine.parse_text(goal)?;
        let frame = InteractiveFrame {
            hyps: Default::default(),
            goal: goal_term,
        };
        Ok(InteractiveSession {
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

    pub fn print(&self) {
        println!("{}", self.monitor_string());
    }

    pub fn current_frame(&self) -> &InteractiveFrame {
        self.frames.last().unwrap()
    }

    pub fn run_tactic(&mut self, line: &str) -> Result<(), tactic::Error> {
        let parts = smart_split(line);
        let mut parts = parts.iter();
        let name = parts.next().unwrap();
        match name.as_str() {
            "intros" => intros(self.engine, self.frames.last_mut().unwrap(), parts.next().unwrap()),
            "rewrite" => rewrite(self.engine, self.frames.last_mut().unwrap(), parts.next().unwrap()),
            "apply" => apply(self, parts.next().unwrap()),
            _ => Err(tactic::Error::UnknownTactic(name.to_string())),
        }
    }

    pub fn solve_goal(&mut self) {
        self.frames.pop();
    }

    pub fn is_finished(&self) -> bool {
        self.frames.is_empty()
    }
}