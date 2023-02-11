import { useContext, useEffect, useRef, useState } from "react";
import { getActionHint, getNatural, sendTactic, subscribe } from "../../../hakim";
import { g } from "../../../i18n";
import { CopyButton } from "../../util/CopyButton";
import { ProofContext } from "../Proof";
import css from "./Sidebar.module.css";

export const History = ({ onNatural }: { onNatural: (x: string) => void }) => {
    const [undos, setUndos] = useState([] as string[]);
    const [redos, setRedos] = useState([] as string[]);
    const [mouseOnRedo, setMouseOnRedo] = useState(false);
    const myRef: any = useRef(null);
    const { setActionHint } = useContext(ProofContext);
    useEffect(() => {
        return subscribe(async (newS) => {
            setUndos(newS.undoHistory);
            setRedos(newS.redoHistory);
            if (mouseOnRedo) {
                setActionHint(await getActionHint(newS.redoHistory[0] || ''));
            }
            myRef.current?.scrollIntoView();
        })
    }, [mouseOnRedo, setActionHint]);
    return (
        <div className={css.base}>
            <ol dir="ltr" className={css.scroll}>
                {undos.map((x, i) => i === undos.length - 1 ? <li key={i} ref={myRef} className={css.current}>{x}</li> : <li key={i}>{x}</li>)}
                {redos.map((x, i) => <li key={i}>{x}</li>)}
            </ol>
            <button onClick={() => sendTactic('Undo')}>{g`undo`}</button>
            <button
                onMouseEnter={async () => {
                    setMouseOnRedo(true);
                    setActionHint(await getActionHint(redos[0] || ''));
                }}
                onMouseLeave={() => {
                    setMouseOnRedo(false);
                    setActionHint(undefined);
                }}
                onClick={() => sendTactic('Redo')}>{g`redo`}</button>
            <CopyButton label={g`export`} text={() => `${localStorage.getItem('last_goal')};\n${undos.join(';\n')};\n`} />
            <button onClick={async () => onNatural(await getNatural())}>{g`in_natural`}</button>
            <button onClick={() => window.history.back()}>{g`exit`}</button>
        </div>
    );
};
