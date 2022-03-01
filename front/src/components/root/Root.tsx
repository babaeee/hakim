import { useState } from "react";
import { sendTactic, setGoal, toBackup } from "../../hakim";
import { isRTL } from "../../i18n";
import { MainMenu } from "../mainmenu/MainMenu";
import { Proof } from "../proof/Proof";
import { Sandbox } from "../sandbox/Sandbox";
import css from "./Root.module.css";

export type State = {
    mode: 'sandbox' | 'proof' | 'mainmenu',
};

const storedState = (): State => {
    const json = localStorage.getItem('reactState');
    if (json) {
        return JSON.parse(json);
    } else {
        return { mode: 'mainmenu' };
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
            {s.mode === 'mainmenu' && <MainMenu onFinish={async (mode) => {
                setS({ mode });
            }} />}
            {s.mode === 'sandbox' && <Sandbox onFinish={async (goal) => {
                if (!goal) {
                    setS({ mode: 'mainmenu' });
                    return;
                }
                goal = goal.trim();
                if (goal.startsWith('Goal')) {
                    const [g, , ...v] = goal.split('.');
                    if (!await setGoal(g.slice(6, -1))) {
                        return;
                    }
                    for (const xs of v) {
                        const x = xs.trim();
                        if (x === '') continue;
                        if (!await sendTactic(x)) {
                            return;
                        }
                    }
                    setS({ mode: 'proof' });
                    return;
                }
                if (await setGoal(goal)) setS({ mode: 'proof' });
            }} />}
            {s.mode === 'proof' && <Proof onFinish={() => {
                setS({ mode: 'sandbox' });
            }} />}
        </div>
    );;
};
