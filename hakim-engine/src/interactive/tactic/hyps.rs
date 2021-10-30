use super::{get_one_arg, Error::*, Result};
use crate::interactive::Frame;

pub fn add_hyp(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "add_hyp")?;
    let term = frame.engine.parse_text(&exp)?;
    let mut frame2 = frame.clone();
    frame.add_hyp_with_name(&frame.engine.generate_name("H"), term.clone())?;
    frame2.goal = term;
    Ok(vec![frame, frame2])
}

pub fn remove_hyp(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "remove_hyp")?;
    if frame.hyps.remove(&exp).is_none() {
        return Err(UnknownHyp(exp));
    }
    Ok(vec![frame])
}
