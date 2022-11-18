use im::vector;
use serde::{Deserialize, Serialize};

use crate::brain::{contains_wild, predict_axiom, TermRef};

use crate::engine::{Engine, Error};
use crate::interactive::suggest::Applicablity;
use crate::library::{engine_from_middle_of_lib, proof_of_theorem};
use crate::parser::is_whity_char;

#[cfg(test)]
mod tests;

mod action_of_tactic;
mod history_auto;
mod monitor;
mod natural;
mod proof_tree;
pub mod suggest;
pub mod tactic;

use tactic::{add_hyp, apply, destruct, intros, lia, lra, replace, rewrite};

use self::action_of_tactic::GraphicalAction;
use self::history_auto::history_lookup_auto;
use self::monitor::Monitor;
use self::natural::NaturalProof;
use self::suggest::{
    suggest_on_goal, suggest_on_goal_dblclk, suggest_on_hyp, suggest_on_hyp_dblclk,
};

pub use self::action_of_tactic::action_of_tactic;
pub use self::suggest::{SuggClass, SuggRule, Suggestion};
use self::tactic::{
    add_from_lib, assumption, auto_list, auto_set, chain, remove_hyp, revert, unfold,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Hyp {
    pub ty: TermRef,
    name: String,
    from_lib: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Frame {
    pub goal: TermRef,
    pub hyps: im::Vector<Hyp>,
    pub engine: Engine,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Snapshot {
    pub frames: im::Vector<Frame>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct HistoryRecord {
    tactic: String,
    snapshot: Snapshot,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Session {
    history: im::Vector<HistoryRecord>,
    /// frames that will used for redo
    undone: im::Vector<HistoryRecord>,
}

fn smart_split(text: &str) -> Vec<String> {
    let mut r = vec![];
    let mut s = "".to_string();
    let mut d = 0;
    let mut in_string = false;
    for c in text.chars() {
        if c == '\'' || c == '"' {
            in_string = !in_string;
        }
        if !in_string && (c == '(' || c == '[') {
            d += 1;
        }
        if !in_string && (c == ')' || c == ']') {
            d -= 1;
        }
        if d != 0 {
            s.push(c);
            continue;
        }
        if is_whity_char(c) {
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

impl Session {
    pub fn new(engine: Engine, goal: &str) -> Result<Self, Error> {
        let snapshot = Snapshot::new(engine, goal)?;
        let hr = HistoryRecord {
            snapshot,
            tactic: "Proof".to_string(),
        };
        Ok(Session {
            history: vector![hr],
            undone: vector![],
        })
    }

    pub fn from_middle_of_lib(lib: &str, name: &str, review: bool) -> Option<Self> {
        let (engine, goal) = engine_from_middle_of_lib(lib, name)?;
        let mut r = Self::new(engine, &goal).ok()?;
        if review {
            let proof = proof_of_theorem(lib, name)?;
            for tac in proof {
                r.run_tactic(&tac).ok()?;
            }
            r.run_tactic("UndoAll").ok()?;
        }
        Some(r)
    }

    pub fn initial_engine(&self) -> Engine {
        self.history[0].snapshot.frames[0].engine.clone()
    }

    pub fn last_snapshot(&self) -> &Snapshot {
        &self.history.last().unwrap().snapshot
    }

    pub fn run_tactic(&mut self, line: &str) -> Result<(), tactic::Error> {
        if line.trim() == "UndoAll" {
            while self.undo().is_ok() {}
            return Ok(());
        }
        if line.trim() == "Undo" {
            return self.undo();
        }
        if line.trim() == "Redo" {
            return self.redo();
        }
        let snapshot = self.last_snapshot().run_tactic(line)?;
        self.add_history_record(HistoryRecord {
            tactic: line.to_string(),
            snapshot,
        });
        Ok(())
    }

    pub fn run_suggestion(
        &mut self,
        sugg: Suggestion,
        ans: Vec<String>,
    ) -> Result<(), tactic::Error> {
        assert_eq!(sugg.questions.len(), ans.len());
        let mut tactic = sugg.tactic;
        for (i, a) in ans.iter().enumerate() {
            tactic = tactic.replace(&format!("${}", i), a);
        }
        self.run_tactic(&tactic)?;
        Ok(())
    }

    pub fn monitor_string(&self) -> String {
        self.last_snapshot().monitor_string()
    }

    pub fn monitor(&self, html: bool) -> Monitor {
        self.last_snapshot().monitor(html)
    }

    pub fn natural(&self) -> String {
        let mut r = String::new();
        NaturalProof::from(self.clone()).into_string(0, &mut r);
        r
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
        let record = self.history.pop_back().unwrap();
        self.undone.push_front(record);
        Ok(())
    }

    pub fn redo(&mut self) -> Result<(), tactic::Error> {
        let x = self.undone.pop_front().ok_or(tactic::Error::CanNotRedo)?;
        self.history.push_back(x);
        Ok(())
    }

    fn add_history_record(&mut self, r: HistoryRecord) {
        self.history.push_back(r);
        self.undone = vector![]; // clear redo tasks
    }

    pub fn get_history(&self) -> (Vec<String>, Vec<String>) {
        (
            self.history.iter().map(|x| x.tactic.clone()).collect(),
            self.undone.iter().map(|x| x.tactic.clone()).collect(),
        )
    }

    pub fn suggest_on_goal_dblclk(&self) -> Option<Suggestion> {
        let frame = self.last_snapshot().clone().pop_frame();
        frame.suggest_on_goal_dblclk()
    }

    pub fn suggest_on_goal_menu(&self) -> Vec<Suggestion> {
        let frame = self.last_snapshot().clone().pop_frame();
        frame.suggest_on_goal_menu()
    }

    pub fn suggest_on_hyp_dblclk(&self, hyp_name: &str) -> Option<Suggestion> {
        let frame = self.last_snapshot().clone().pop_frame();
        frame.suggest_on_hyp_dblclk(hyp_name)
    }

    pub fn suggest_on_hyp_menu(&self, hyp_name: &str) -> Vec<Suggestion> {
        let frame = self.last_snapshot().clone().pop_frame();
        frame.suggest_on_hyp_menu(hyp_name)
    }

    pub fn history_based_auto(&self) -> Option<Vec<String>> {
        history_lookup_auto(self.clone())
    }

    pub fn pos_of_span_hyp(&self, hyp_name: &str, span: (usize, usize)) -> Option<usize> {
        self.last_snapshot()
            .last_frame()?
            .pos_of_span_hyp(hyp_name, span)
    }

    pub fn pos_of_span_goal(&self, span: (usize, usize)) -> Option<usize> {
        self.last_snapshot().last_frame()?.pos_of_span_goal(span)
    }

    pub fn try_auto(&self) -> Option<String> {
        if self.is_finished() {
            return None;
        }
        self.last_snapshot().last_frame()?.try_auto()
    }

    pub fn action_of_tactic(&self, tactic: &str) -> Option<GraphicalAction> {
        action_of_tactic(self, tactic)
    }
}

impl From<Frame> for Snapshot {
    fn from(frame: Frame) -> Self {
        Self {
            frames: vector![frame],
        }
    }
}

impl Snapshot {
    pub fn new(engine: Engine, goal: &str) -> Result<Snapshot, Error> {
        let goal_term = engine.parse_text(goal)?;
        if contains_wild(&goal_term) {
            return Err(Error::GoalWithWildCard(goal_term));
        }
        let frame = Frame {
            hyps: Default::default(),
            goal: goal_term,
            engine,
        };
        Ok(frame.into())
    }

    pub fn monitor_string(&self) -> String {
        if self.is_finished() {
            return "No more subgoals.".to_string();
        }
        self.monitor(false).to_string()
    }

    pub fn run_tactic(&self, line: &str) -> Result<Self, tactic::Error> {
        if let Some(x) = line.strip_prefix("Switch ") {
            let t: usize = x.parse().map_err(|_| tactic::Error::BadArg {
                arg: x.to_string(),
                tactic_name: "Switch".to_string(),
            })?;
            return self.switch_frame(t);
        }
        let mut snapshot = self.clone();
        if let Some(x) = line.strip_prefix("Seq ") {
            let tacs = smart_split(x);
            for tac in tacs {
                if let Some(tac) = tac.strip_prefix('(') {
                    if let Some(tac) = tac.strip_suffix(')') {
                        snapshot = snapshot.run_tactic(tac)?;
                    } else {
                        unreachable!("smart split is broken");
                    }
                } else {
                    snapshot = snapshot.run_tactic(&tac)?;
                }
            }
            return Ok(snapshot);
        }
        let frame = snapshot.pop_frame();
        let new_frames = frame.run_tactic(line)?;
        snapshot.frames.extend(new_frames);
        Ok(snapshot)
    }

    pub fn last_frame(&self) -> Option<&Frame> {
        self.frames.last()
    }

    pub fn pop_frame(&mut self) -> Frame {
        self.frames.pop_back().unwrap()
    }

    fn switch_frame(&self, i: usize) -> tactic::Result<Self> {
        let mut result = self.clone();
        if i >= result.frames.len() {
            return Err(tactic::Error::InvalidGoalNumber {
                i,
                n: result.frames.len(),
            });
        }
        result
            .frames
            .swap(result.frames.len() - 1, result.frames.len() - 1 - i);
        Ok(result)
    }

    pub fn is_finished(&self) -> bool {
        self.frames.is_empty()
    }
}

impl Frame {
    pub fn add_hyp_with_name(&mut self, name: &str, ty: TermRef) -> tactic::Result<()> {
        self.engine.add_axiom_with_term(name, ty.clone(), 0)?;
        let hyp = Hyp {
            name: name.to_string(),
            ty,
            from_lib: false,
        };
        self.hyps.push_back(hyp);
        Ok(())
    }
    pub fn add_hyp_with_name_in_index(
        &mut self,
        name: &str,
        ty: TermRef,
        index: usize,
    ) -> tactic::Result<()> {
        self.add_hyp_with_name(name, ty)?;
        let hyp = self.hyps.pop_back().unwrap();
        self.hyps.insert(index, hyp);
        Ok(())
    }
    pub fn get_hyp_by_name(&self, name: &str) -> Option<&Hyp> {
        self.hyps.iter().find(|x| x.name == name)
    }

    pub fn deny_dependency(&self, name: &str) -> tactic::Result<()> {
        if let Some(hyp) = self.get_hyp_by_name(name) {
            if hyp.from_lib {
                return Err(tactic::Error::HypIsFromLib(name.to_string()));
            }
        }
        for hyp in &self.hyps {
            if predict_axiom(&hyp.ty, |x| x == name) {
                return Err(tactic::Error::ContextDependOnHyp(
                    name.to_string(),
                    hyp.ty.clone(),
                ));
            }
        }
        if predict_axiom(&self.goal, |x| x == name) {
            return Err(tactic::Error::ContextDependOnHyp(
                name.to_string(),
                self.goal.clone(),
            ));
        }
        Ok(())
    }

    pub fn remove_hyp_with_name(&mut self, name: &str) -> tactic::Result<Hyp> {
        self.deny_dependency(name)?;
        if let Some((i, _)) = self.hyps.iter().enumerate().find(|(_, x)| x.name == name) {
            return self.remove_hyp_with_index(i);
        }
        Err(tactic::Error::UnknownHyp(name.to_string()))
    }
    pub fn remove_hyp_with_index(&mut self, index: usize) -> tactic::Result<Hyp> {
        let hyp = self
            .hyps
            .get(index)
            .ok_or_else(|| tactic::Error::UnknownHyp(index.to_string()))?;
        self.deny_dependency(&hyp.name)?;
        self.engine.remove_name_unchecked(&hyp.name);
        let hyp = self.hyps.remove(index);
        Ok(hyp)
    }

    pub fn suggest_on_goal_dblclk(&self) -> Option<Suggestion> {
        suggest_on_goal_dblclk(&self.goal, self)
    }

    pub fn suggest_on_goal_menu(&self) -> Vec<Suggestion> {
        suggest_on_goal(&self.goal, self)
    }

    pub fn suggest_on_hyp_dblclk(&self, hyp_name: &str) -> Option<Suggestion> {
        suggest_on_hyp_dblclk(self, hyp_name)
    }

    pub fn suggest_on_hyp_menu(&self, hyp_name: &str) -> Vec<Suggestion> {
        suggest_on_hyp(self, hyp_name)
    }
    pub fn run_tactic(&self, line: &str) -> Result<Vec<Self>, tactic::Error> {
        let parts = smart_split(line);
        let mut parts = parts.iter().map(|x| x.as_str());
        let name = parts.next().ok_or(tactic::Error::EmptyTactic)?;
        if self.engine.is_disabled_tactic(name) {
            return Err(tactic::Error::DisabledTactic(name.to_string()));
        }
        let frame = self.clone();
        match name {
            "intros" => intros(frame, parts),
            "rewrite" => rewrite(frame, parts),
            "replace" => replace(frame, parts),
            "unfold" => unfold(frame, parts),
            "apply" => apply(frame, parts),
            "add_hyp" => add_hyp(frame, parts),
            "remove_hyp" => remove_hyp(frame, parts),
            "revert" => revert(frame, parts),
            "chain" => chain(frame, parts),
            "destruct" => destruct(frame, parts),
            "add_from_lib" => add_from_lib(frame, parts),
            "lia" => lia(frame),
            "lra" => lra(frame),
            "auto_set" => auto_set(frame),
            "auto_list" => auto_list(frame),
            "assumption" => assumption(frame),
            _ => Err(tactic::Error::UnknownTactic(name.to_string())),
        }
    }

    pub fn pos_of_span_hyp(&self, hyp_name: &str, span: (usize, usize)) -> Option<usize> {
        let hyp = &self.get_hyp_by_name(hyp_name)?.ty;
        self.engine.pos_of_span(hyp, span)
    }

    pub fn pos_of_span_goal(&self, span: (usize, usize)) -> Option<usize> {
        self.engine.pos_of_span(&self.goal, span)
    }

    pub fn try_auto(&self) -> Option<String> {
        const AUTO_TAC: &[&str] = &["assumption", "auto_set", "auto_list", "lia", "lra"];
        for tac in AUTO_TAC {
            if self.run_tactic(tac).ok().filter(|x| x.is_empty()).is_some() {
                return Some(tac.to_string());
            }
        }
        let suggs = suggest_on_goal(&self.goal, self)
            .into_iter()
            .filter(|x| x.applicablity == Applicablity::Auto);
        for sugg in suggs {
            assert!(sugg.questions.is_empty());
            if let Ok(nf) = self.run_tactic(&sugg.tactic) {
                if nf.is_empty() {
                    return Some(sugg.tactic);
                }
            }
        }
        None
    }
}
