import { useState } from "react";
import { setGoal } from "../../hakim";
import { Proof } from "../proof/Proof";
import { Sandbox } from "../sandbox/Sandbox";

type State = {
    mode: 'sandbox' | 'proof',
};

export const Root = () => {
    const [s, setS] = useState({ mode: 'sandbox' } as State);
    if (s.mode === 'sandbox') {
        return <Sandbox onFinish={(goal) => {
            if (setGoal(goal)) setS({ mode: 'proof' });
        }} />;
    }
    return <Proof onFinish={() => {
        setS({ mode: 'sandbox' });
    }} />;
};
