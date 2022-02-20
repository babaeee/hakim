import { useContext, useEffect, useState } from "react";
import { runSuggDblGoal, runSuggDblHyp, runSuggMenuGoal, runSuggMenuHyp, sendTactic, State, subscribe, suggMenuGoal, suggMenuHyp, tryTactic } from "../../../hakim";
import css from "./Monitor.module.css";
import { useMenuState, ControlledMenu, MenuItem } from "@szhsin/react-menu";
import '@szhsin/react-menu/dist/index.css';
import { g } from "../../../i18n";
import { useDrag, useDrop } from 'react-dnd'
import classNames from "classnames";
import { ProofContext } from "../Proof";
import { normalPrompt } from "../../../dialog";

type HypProps = {
    name: string,
    ty: string,
};

const Hyp = ({ name, ty }: HypProps): JSX.Element => {
    const { toggleMenu, ...menuProps } = useMenuState();
    const [anchorPoint, setAnchorPoint] = useState({ x: 0, y: 0 });
    const [suggs, setSuggs] = useState([] as string[]);
    const { setReplaceMode, replaceMode } = useContext(ProofContext);
    const [, drag] = useDrag(() => ({
        type: 'Hyp',
        item: () => ({ name }),
    }), [name, ty]);
    const [{ isOver, canDrop }, drop] = useDrop(
        () => ({
            accept: 'Hyp',
            drop: (x: any) => {
                sendTactic(`apply ${x.name} in ${name}`);
            },
            canDrop: (x: any) => x.name !== name && tryTactic(`apply ${x.name} in ${name}`),
            collect: (monitor) => ({
                isOver: !!monitor.isOver(),
                canDrop: !!monitor.canDrop()
            }),
        }),
        [name],
    );
    return (
        <div ref={!replaceMode ? drop : undefined}>
            <div ref={!replaceMode ? drag : undefined} className={classNames({
                [css.hyp]: true,
                [css.drop]: canDrop,
                [css.over]: isOver,
            })} onContextMenu={(e) => {
                e.preventDefault();
                setSuggs(suggMenuHyp(name));
                setAnchorPoint({ x: e.clientX, y: e.clientY });
                toggleMenu(true);
            }}
                onDoubleClick={() => runSuggDblHyp(name)}>
                {name}: <span className={classNames({ [css.selectEnable]: replaceMode })}
                    onMouseUp={async (e) => {
                        const sel = window.getSelection();
                        if (!sel) return;
                        if (sel.toString() === '') return;
                        if (!(sel.anchorNode?.parentElement === e.target)) return;
                        const range = sel.getRangeAt(0);
                        const start = range.startOffset;
                        const end = range.endOffset;
                        const userInp = await normalPrompt(g`replace_with_what1 ${ty.slice(start, end)} replace_with_what2`);
                        sendTactic(`add_hyp ((${ty.slice(start, end)}) = (${userInp}))`);
                        setReplaceMode(false);
                    }}
                >{ty}</span>
                <ControlledMenu {...menuProps} anchorPoint={anchorPoint}
                    onClose={() => toggleMenu(false)}>
                    {suggs.map((x, i) => <MenuItem onClick={() => runSuggMenuHyp(name, i)}>{x}</MenuItem>)}
                </ControlledMenu>
            </div>
        </div>
    );
};


const Goal = ({ ty }: { ty: string }): JSX.Element => {
    const { toggleMenu, ...menuProps } = useMenuState();
    const [anchorPoint, setAnchorPoint] = useState({ x: 0, y: 0 });
    const [suggs, setSuggs] = useState([] as string[]);
    const { setReplaceMode, replaceMode } = useContext(ProofContext);
    const [{ isOver, canDrop }, drop] = useDrop(
        () => ({
            accept: 'Hyp',
            drop: (x: any) => { sendTactic(`apply ${x.name}`); },
            canDrop: (x: any) => tryTactic(`apply ${x.name}`),
            collect: (monitor) => ({
                isOver: !!monitor.isOver(),
                canDrop: !!monitor.canDrop(),
            }),
        }),
        [],
    );
    return (
        <div ref={!replaceMode ? drop : undefined}
            className={classNames({
                [css.hyp]: true,
                [css.selectEnable]: replaceMode,
                [css.drop]: canDrop,
                [css.over]: isOver,
            })}
            onMouseUp={async (e) => {
                const sel = window.getSelection();
                if (!sel) return;
                if (sel.toString() === '') return;
                if (!(sel.anchorNode?.parentElement === e.target)) return;
                const range = sel.getRangeAt(0);
                const start = range.startOffset;
                const end = range.endOffset;
                const len = end - start;
                const text = ty.slice(start, end);
                let cnt = 1;
                for (let i = 0; i < start; i += 1) {
                    if (ty.slice(i, i + len) === text) {
                        cnt += 1;
                    }
                }
                const userInp = await normalPrompt(g`replace_with_what1 ${text} replace_with_what2`);
                sendTactic(`replace #${cnt} (${text}) with (${userInp})`);
                setReplaceMode(false);
            }}
            onDoubleClick={() => runSuggDblGoal()} onContextMenu={e => {
                e.preventDefault();
                setSuggs(suggMenuGoal());
                setAnchorPoint({ x: e.clientX, y: e.clientY });
                toggleMenu(true);
            }}>
            {ty}
            <ControlledMenu {...menuProps} anchorPoint={anchorPoint}
                onClose={() => toggleMenu(false)}>
                {suggs.map((x, i) => <MenuItem onClick={() => runSuggMenuGoal(i)}>{x}</MenuItem>)}
            </ControlledMenu>
        </div>
    );
};

const NextGoal = ({ ty, i }: { ty: string, i: number }) => {
    return (
        <div className={css.hyp} onDoubleClick={() => sendTactic(`Switch ${i + 1}`)}>
            {ty}
        </div>
    )
};

export const Monitor = () => {
    const { onFinish } = useContext(ProofContext);
    const [s, setS] = useState(undefined as State | undefined);
    useEffect(() => {
        return subscribe((newS) => {
            setS(newS);
        })
    }, []);
    if (!s) {
        return <div className={css.monitor}>Loading...</div>;
    }
    if (s.isFinished) {
        return <div className={css.monitor}>
            {g`no_more_subgoal`}
            <button onClick={onFinish}>{g`exit`}</button>
        </div>;
    }
    const { hyps, goals } = s.monitor;
    const goalsR = [...goals].reverse();
    return (
        <div className={css.monitor} dir="ltr">
            {hyps.map(([name, ty]: any) => (
                <Hyp name={name} ty={ty} />
            ))}
            <hr /><Goal ty={goalsR[0]} />
            {goalsR.slice(1).map((goal: any, i: number) => (
                <><hr /><NextGoal ty={goal} i={i} /></>
            ))}
        </div>
    )
};