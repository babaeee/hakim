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
import { isDebug } from "../../../dev_mode";
import { subscribeKeyboard } from "../../../keyboard";

type HypProps = {
    name: string,
    ty: string,
    mode: Mode,
    setMode: (x: Mode) => any,
};

type Sugg = {
    label: string,
    debugInfo?: string | undefined,
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
    ty = ty.replaceAll(/<span [^>]*>/g, '');
    ty = ty.replaceAll('</span>', '');
    console.log(ty);
    const sel = window.getSelection();
    console.log(sel);
    if (!sel) return;
    if (sel.toString() === '') return;
    console.log(sel.anchorNode);
    console.log(e.target);
    // if (sel.anchorNode !== e.target?.parentElement
    //     && sel.anchorNode?.parentElement !== e.target?.parentElement
    //     && sel.anchorNode?.parentElement?.parentElement !== e.target
    //     && sel.anchorNode?.parentElement?.parentElement?.parentElement !== e.target
    //     && sel.anchorNode?.parentElement?.parentElement !== e.target?.parentElement
    //     && sel.anchorNode?.parentElement?.parentElement !== e.target?.parentElement?.parentElement) return;
    const range = sel.getRangeAt(0);
    console.log(range);
    console.log(range.toString());
    const dbg = (t: any, x: any) => {
        console.log(`dbg ${t}: ${x}`);
        return x;
    }
    const offsetOfNode = (node: Node): number => {
        if (node.parentElement?.dataset.pos) {
            return dbg(1, Number(node.parentElement?.dataset.pos));
        }
        if (node.previousSibling && node.previousSibling instanceof HTMLElement) {
            return dbg(2, Number(node.previousSibling?.dataset.pos) + node.previousSibling.innerText.length);
        }
        return 0;
    }
    let start = range.startOffset + offsetOfNode(range.startContainer);
    let end = range.endOffset + offsetOfNode(range.endContainer);
    while (ty[start] === ' ') start += 1;
    while (ty[end - 1] === ' ') end -= 1;
    const text = sel.toString().trim().replaceAll('\u2068', '').replaceAll('\u2069', '').replaceAll(/\s+/g, ' ');
    for (let i = 0; i < ty.length; i += 1) {
        if (ty[i] === '\u2068' || ty[i] === '\u2069') {
            if (i <= start) start -= 1;
            if (i <= end) end -= 1;
        }
    }
    end = start + text.length;
    const dummyReplace = replaceTactic({ start, end, text, userInp: '2' });
    setSuggs([{
        label: text,
        debugInfo: `(${start}, ${end})`,
        disabled: true,
        action: () => { },
    }, {
        label: g`copy`,
        action: async () => {
            await navigator.clipboard.writeText(text);
        },
    }, {
        label: g`replace`,
        disabled: dummyReplace === undefined,
        debugInfo: dummyReplace,
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

const DblClickHere = () => {
    return <div className={css.dblClickHere}>🖰{g`double_click_here`}</div>;
};

const MyControlledMenu = ({ menuProps, anchorPoint, suggs, toggleMenu }: any) => {
    return (
        <ControlledMenu {...menuProps} anchorPoint={anchorPoint}
            onClose={() => toggleMenu(false)}>
            {suggs.length === 0 && <MenuItem disabled>{g`no_suggestion`}</MenuItem>}
            {suggs.map((x: Sugg) => <MenuItem key={x.label} disabled={x.disabled} onClick={x.action}>
                {x.label}
                {isDebug() && <><br />{x.debugInfo}</>}
            </MenuItem>)}
        </ControlledMenu>
    );
};

const Hyp = ({ name, ty, mode, setMode }: HypProps): JSX.Element => {
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
                    if (mode === 'delete') {
                        sendTactic(`remove_hyp ${name}`);
                        setMode('normal');
                    }
                    if (mode === 'revert') {
                        sendTactic(`revert ${name}`);
                        setMode('normal');
                    }
                    // prevent text select in double clicks
                    if (e.detail === 2) {
                        e.preventDefault();
                    }
                }}
                onDoubleClick={() => runSuggDblHyp(name)}>
                <span ref={drag} className={css.dragHandler}>&#x25CE;</span>{' '}
                {name}: <span className={css.ty} dangerouslySetInnerHTML={{ __html: ty }} />
                <MyControlledMenu
                    toggleMenu={toggleMenu}
                    menuProps={menuProps}
                    anchorPoint={anchorPoint}
                    suggs={suggs}
                />
            </div>
        </div>
    );
};


const Goal = ({ ty }: { ty: string }): JSX.Element => {
    const { toggleMenu, ...menuProps } = useMenuState();
    const [anchorPoint, setAnchorPoint] = useState({ x: 0, y: 0 });
    const [suggs, setSuggs] = useState([] as Sugg[]);
    const { actionHint } = useContext(ProofContext);
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
            <span className={css.ty} dangerouslySetInnerHTML={{ __html: ty }} />
            {actionHint?.kind === 'dblClick' && actionHint.target.kind === 'goal' && <DblClickHere />}
            <MyControlledMenu
                toggleMenu={toggleMenu}
                menuProps={menuProps}
                anchorPoint={anchorPoint}
                suggs={suggs}
            />
        </div>
    );
};

const NextGoal = ({ ty, i }: { ty: string, i: number }) => {
    return (
        <div className={css.nextGoal} onDoubleClick={() => sendTactic(`Switch ${i + 1}`)}>
            <span className={css.ty} dangerouslySetInnerHTML={{ __html: ty }} />
        </div>
    )
};

type Mode = "normal" | "delete" | "revert";

export const Monitor = () => {
    const { onFinish, actionHint } = useContext(ProofContext);
    const [s, setS] = useState(undefined as State | undefined);
    const [mode, setMode] = useState('normal' as Mode);
    useEffect(() => {
        return subscribe((newS) => {
            setS(newS);
        })
    }, []);
    useEffect(() => {
        const handleKeyDown = (event: KeyboardEvent) => {
            console.log(event.code);
            if (event.ctrlKey && event.shiftKey && event.code === 'KeyZ') {
                sendTactic('UndoAll');
            } else if (event.ctrlKey && event.code === 'KeyZ') {
                sendTactic('Undo');
            } else if (event.ctrlKey && event.code === 'KeyY') {
                sendTactic('Redo');
            } else if (event.code === 'KeyR') {
                setMode('revert');
            } else if (event.code === 'Delete') {
                setMode('delete');
            } else if (event.code === 'Escape') {
                setMode('normal');
            }
        }
        return subscribeKeyboard(1, handleKeyDown);
    });
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
                <Hyp mode={mode} setMode={setMode} name={name} ty={ty} />
            ))}
            <hr /><Goal ty={goalsR[0]} />
            {goalsR.slice(1).map((goal: any, i: number) => (
                <><hr style={{ filter: "opacity(0.2)" }} /><NextGoal ty={goal} i={i} /></>
            ))}
            {mode === 'delete' && <>{g`select_a_hyp_to_delete`}</>}
            {mode === 'revert' && <>{g`select_a_hyp_to_revert`}</>}
            {isDebug() && <div>action hint: {JSON.stringify(actionHint)}</div>}
        </div>
    );
};
