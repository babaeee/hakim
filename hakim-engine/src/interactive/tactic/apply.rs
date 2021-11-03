use std::collections::HashMap;

use crate::{
    app_ref,
    brain::{
        contains_wild, get_forall_depth,
        infer::{match_and_infer, type_of_and_infer, InferResults},
        normalize, predict_axiom, type_of,
    },
    engine::Engine,
    interactive::Frame,
    term_ref, TermRef,
};

use super::{Error::*, Result};

fn parse_other_args(
    args: impl Iterator<Item = String>,
    engine: &Engine,
) -> Result<(HashMap<usize, TermRef>, Option<String>)> {
    let mut r = HashMap::default();
    let mut it = args;
    while let Some(arg) = it.next() {
        let c = || BadArg {
            arg: arg.clone(),
            tactic_name: "apply".to_string(),
        };
        if arg == "in" {
            let hyp = it.next().ok_or_else(|| UnknownHyp("".to_string()))?;
            return Ok((r, Some(hyp)));
        }
        let mut chars = arg.chars();
        if chars.next() != Some('(') {
            return Err(c());
        }
        if chars.next_back() != Some(')') {
            return Err(c());
        }
        let arg = chars.as_str();
        let (num, val) = arg.split_once(":=").ok_or_else(c)?;
        let num = num.parse::<usize>().map_err(|_| c())?;
        r.insert(num, engine.parse_text(val)?);
    }
    Ok((r, None))
}

fn apply_for_hyp(mut frame: Frame, exp: &str, name: String) -> Result<Vec<Frame>> {
    let (term, ic) = frame.engine.parse_text_with_wild(exp)?;
    let prev_hyp = frame.remove_hyp_with_name(name.clone())?;
    let mut infers = InferResults::new(ic);
    let ty = type_of_and_infer(app_ref!(term, term_ref!(axiom name, prev_hyp)), &mut infers)?;
    for i in 0..ic {
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        todo!();
    }
    let ty = infers.fill(ty);
    if predict_axiom(&ty, &|x| x == name) {
        return Err(ContextDependOnHyp(name, ty));
    }
    frame.add_hyp_with_name(&name, ty)?;
    Ok(vec![frame])
}

fn apply_for_goal(
    frame: Frame,
    exp: &str,
    mut other_args: HashMap<usize, TermRef>,
) -> Result<Vec<Frame>> {
    let term = frame.engine.parse_text(exp)?;
    let ty = type_of(dbg!(term.clone()))?;
    let goal = frame.goal.clone();
    let d_forall = get_forall_depth(&ty) - get_forall_depth(&goal);
    let mut twa = term;
    let mut inf_num = 0;
    for i in 0..d_forall {
        if let Some(x) = other_args.remove(&(i + 1)) {
            twa = app_ref!(twa, x);
        } else {
            twa = app_ref!(twa, term_ref!(_ inf_num));
            inf_num += 1;
        }
    }
    let mut infers = InferResults::new(inf_num);
    let twa_ty = type_of_and_infer(twa, &mut infers)?;
    match_and_infer(twa_ty, goal, &mut infers)?;
    let mut v = vec![];
    for i in 0..inf_num {
        let mut frame = frame.clone();
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        if !contains_wild(&infers.tys[i]) {
            frame.goal = normalize(infers.tys[i].clone());
            v.push(frame);
        } else {
            return Err(CanNotFindInstance(i, ty));
        }
    }
    Ok(v)
}

pub fn apply(frame: Frame, mut args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = &args.next().ok_or(BadArgCount {
        expected: 1,
        found: 0,
        tactic_name: "apply".to_string(),
    })?;
    let (other_args, hyp) = parse_other_args(args, &frame.engine)?;
    if let Some(hyp) = hyp {
        apply_for_hyp(frame, exp, hyp)
    } else {
        apply_for_goal(frame, exp, other_args)
    }
}
