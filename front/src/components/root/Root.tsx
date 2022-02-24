import { useState } from "react";
import { setGoal, toBackup } from "../../hakim";
import { isRTL } from "../../i18n";
import { Proof } from "../proof/Proof";
import { Sandbox } from "../sandbox/Sandbox";
import css from "./Root.module.css";

type State = {
    mode: 'sandbox' | 'proof',
};

const storedState = (): State => {
    const json = localStorage.getItem('reactState');
    if (json) {
        return JSON.parse(json);
    } else {
        return { mode: 'sandbox' };
    }
};

let stateToStore: State = storedState();

window.onbeforeunload = () => {
    localStorage.setItem('reactState', JSON.stringify(stateToStore));
    localStorage.setItem('wasmState', toBackup());
};

export const Root = () => {
    const [s, setSinner] = useState(storedState());
    const setS = (x: State) => {
        stateToStore = x;
        setSinner(x);
    }
    return (
        <div dir={isRTL() ? 'rtl' : 'ltr'} className={css.main}>
            {s.mode === 'sandbox'
                ? <Sandbox onFinish={async (goal) => {
                    if (await setGoal(goal)) setS({ mode: 'proof' });
                }} />
                : <Proof onFinish={() => {
                    setS({ mode: 'sandbox' });
                }} />
            }
        </div>
    );;
};
