import { useState } from "react";
import { setGoal } from "../../hakim";
import { isRTL } from "../../i18n";
import { Proof } from "../proof/Proof";
import { Sandbox } from "../sandbox/Sandbox";
import css from "./Root.module.css";

type State = {
    mode: 'sandbox' | 'proof',
};

export const Root = () => {
    const [s, setS] = useState({ mode: 'sandbox' } as State);
    return (
        <div dir={isRTL() ? 'rtl' : 'ltr'} className={css.main}>
            {s.mode === 'sandbox'
                ? <Sandbox onFinish={(goal) => {
                    if (setGoal(goal)) setS({ mode: 'proof' });
                }} />
                : <Proof onFinish={() => {
                    setS({ mode: 'sandbox' });
                }} />
            }
        </div>
    );;
};
