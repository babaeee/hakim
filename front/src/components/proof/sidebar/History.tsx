import { useEffect, useState } from "react";
import { sendTactic, subscribe } from "../../../hakim";
import { g } from "../../../i18n";
import { CopyButton } from "../../util/CopyButton";
import css from "./Sidebar.module.css";

export const History = () => {
    const [s, setS] = useState([] as string[]);
    useEffect(() => {
        return subscribe((newS) => {
            setS(newS.history);
        })
    }, []);
    return (
        <div className={css.base}>
            <ul dir="ltr" className={css.scroll}>
                {s.map((x, i) => <li key={i}>{x}</li>)}
            </ul>
            <button onClick={() => sendTactic('Undo')}>{g`undo`}</button>
            <CopyButton label={g`export`} text={() => `${localStorage.getItem('last_goal')}.\n${s.join('.\n')}.\n`} />
        </div>
    );
};