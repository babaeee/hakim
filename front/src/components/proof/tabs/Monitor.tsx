import { useContext, useEffect, useState } from "react";
import { runSuggDblGoal, runSuggDblHyp, sendTactic, spanPosOfGoal, spanPosOfHyp, State, subscribe, suggMenuGoal, suggMenuHyp, tryTactic } from "../../../hakim";
import css from "./Monitor.module.css";
import { useMenuState, ControlledMenu, MenuItem } from "@szhsin/react-menu";
import '@szhsin/react-menu/dist/index.css';
import { g } from "../../../i18n";
import { useDrag, useDrop } from 'react-dnd'
import classNames from "classnames";
import { ProofContext } from "../Proof";
import { normalPrompt } from "../../../dialog";
import "./highlight.css";

type HypProps = {
    name: string,
    ty: string,
};

type Sugg = {
    label: string,
    action: () => void,
    disabled?: boolean,
};

type onSelectLogicType = (x: {
    ty: string,
    setSuggs: (x: Sugg[]) => void,
    setAnchorPoint: (a: { x: number, y: number }) => void,
    toggleMenu: (x: boolean) => void,
    replaceTactic: (x: { start: number, end: number, text: string, userInp: string }) => string | undefined,
}) => (e: any) => Promise<void>;
const onSelectLogic: onSelectLogicType = ({ ty, setSuggs, setAnchorPoint, toggleMenu, replaceTactic }) => async (e) => {
    ty = ty.replaceAll('<span class="highlightLiteral">', '');
    ty = ty.replaceAll('<span class="highlightType">', '');
    ty = ty.replaceAll('<span class="highlightIdent">', '');
    ty = ty.replaceAll('<span class="highlightFunction">', '');
    ty = ty.replaceAll('</span>', '');
    console.log(ty);
    const sel = window.getSelection();
    console.log(sel);
    if (!sel) return;
    if (sel.toString() === '') return;
    if (sel.anchorNode?.parentElement !== e.target
        && sel.anchorNode?.parentElement?.parentElement !== e.target) return;
    const range = sel.getRangeAt(0);
    let start = range.startOffset;
    let end = range.endOffset;
    while (ty[start] === ' ') start += 1;
    while (ty[end - 1] === ' ') end -= 1;
    const text = ty.slice(start, end).trim().replaceAll('\u2068', '').replaceAll('\u2069', '');
    for (let i = 0; i < ty.length; i += 1) {
        if (ty[i] === '\u2068' || ty[i] === '\u2069') {
            if (i <= start) start -= 1;
            if (i <= end) end -= 1;
        }
    }
    setSuggs([{
        label: text,
        disabled: true,
        action: () => { },
    }, {
        label: g`copy`,
        action: async () => {
            await navigator.clipboard.writeText(text);
        },
    }, {
        label: g`replace`,
        action: async () => {
            const userInp = await normalPrompt(g`replace_with_what1 ${text} replace_with_what2`, text);
            const tac = replaceTactic({ start, end, text, userInp });
            if (!tac) return;
            sendTactic(tac);
        },
    }]);
    setAnchorPoint({ x: e.clientX, y: e.clientY });
    toggleMenu(true);
};

const Hyp = ({ name, ty }: HypProps): JSX.Element => {
    const { toggleMenu, ...menuProps } = useMenuState();
    const [anchorPoint, setAnchorPoint] = useState({ x: 0, y: 0 });
    const [suggs, setSuggs] = useState([] as Sugg[]);
    const [, drag, preview] = useDrag(() => ({
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
        <div ref={drop}>
            <div ref={preview}
                className={classNames({
                    [css.hyp]: true,
                    [css.drop]: canDrop,
                    [css.over]: isOver,
                })}
                onContextMenu={(e) => {
                    e.preventDefault();
                    setSuggs(suggMenuHyp(name));
                    setAnchorPoint({ x: e.clientX, y: e.clientY });
                    toggleMenu(true);
                }}
                onMouseUp={onSelectLogic({
                    ty, setAnchorPoint, setSuggs, toggleMenu,
                    replaceTactic: ({ start, end, text, userInp }) => {
                        let cnt = spanPosOfHyp(name, start, end);
                        if (!cnt) return;
                        return `replace #${cnt} (${text}) with (${userInp}) in ${name}`;
                    },
                })}
                onMouseDown={(e) => {
                    // prevent text select in double clicks
                    if (e.detail === 2) {
                        e.preventDefault();
                    }
                }}
                onDoubleClick={() => runSuggDblHyp(name)}>
                <span ref={drag} className={css.dragHandler}>&#x25CE;</span>{' '}
                {name}: <span dangerouslySetInnerHTML={{ __html: ty }} />
                <ControlledMenu {...menuProps} anchorPoint={anchorPoint}
                    onClose={() => toggleMenu(false)}>
                    {suggs.length === 0 && <MenuItem disabled>{g`no_suggestion`}</MenuItem>}
                    {suggs.map((x, i) => <MenuItem key={x.label} disabled={x.disabled} onClick={x.action}>{x.label}</MenuItem>)}
                </ControlledMenu>
            </div>
        </div>
    );
};


const Goal = ({ ty }: { ty: string }): JSX.Element => {
    const { toggleMenu, ...menuProps } = useMenuState();
    const [anchorPoint, setAnchorPoint] = useState({ x: 0, y: 0 });
    const [suggs, setSuggs] = useState([] as Sugg[]);
    useEffect(() => {
        const handleKeyDown = (event: KeyboardEvent) => {
            console.log(event.code);
            if (event.ctrlKey && event.code === 'KeyZ') {
                sendTactic('Undo');
            }
        }

        window.addEventListener("keydown", handleKeyDown);
        return () => window.removeEventListener("keydown", handleKeyDown);
    });
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
        <div ref={drop}
            className={classNames({
                [css.hyp]: true,
                [css.drop]: canDrop,
                [css.over]: isOver,
            })}
            onMouseUp={onSelectLogic({
                ty, setAnchorPoint, setSuggs, toggleMenu,
                replaceTactic: ({ start, end, text, userInp }) => {
                    const cnt = spanPosOfGoal(start, end);
                    if (!cnt) return;
                    return `replace #${cnt} (${text}) with (${userInp})`;
                },
            })}
            onDoubleClick={() => runSuggDblGoal()}
            onMouseDown={(e) => {
                // prevent text select in double clicks
                if (e.detail === 2) {
                    e.preventDefault();
                }
            }}
            onContextMenu={e => {
                e.preventDefault();
                setSuggs(suggMenuGoal());
                setAnchorPoint({ x: e.clientX, y: e.clientY });
                toggleMenu(true);
            }}>
            <span dangerouslySetInnerHTML={{ __html: ty }} />
            <ControlledMenu {...menuProps} anchorPoint={anchorPoint}
                onClose={() => toggleMenu(false)}>
                {suggs.length === 0 && <MenuItem disabled>{g`no_suggestion`}</MenuItem>}
                {suggs.map((x) => <MenuItem key={x.label} disabled={x.disabled} onClick={x.action}>{x.label}</MenuItem>)}
            </ControlledMenu>
        </div>
    );
};

const NextGoal = ({ ty, i }: { ty: string, i: number }) => {
    return (
        <div className={css.hyp} onDoubleClick={() => sendTactic(`Switch ${i + 1}`)}>
            <span dangerouslySetInnerHTML={{ __html: ty }} />
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
            <button onClick={() => onFinish(true)}>{g`exit`}</button>
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