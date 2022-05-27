import { useEffect, useState } from "react";
import { normalPrompt } from "../../dialog";
import { sendTactic, subscribe, tryAuto, TryAutoResult } from "../../hakim";
import { g } from "../../i18n";
import css from "./toolbar.module.css";

export const ToolButton = ({ label, onClick }: { label: string, onClick: any }) => {
    return (
        <button className={css.toolButton} onClick={onClick}>
            {label}
        </button>
    );
}

const newAssert = async () => {
    const inp = await normalPrompt(g`input_assertion`);
    sendTactic(`add_hyp (${inp})`);
};

let isWorking = false;

const AutoProofButton = () => {
    const [s, setS] = useState({ available: false } as TryAutoResult);
    const [mode, setMode] = useState('normal' as 'boost' | 'normal');
    useEffect(() => {
        return subscribe(async () => {
            // lock this function so it won't be multiple instances of it sending tactics
            while (isWorking) {
                await new Promise((res) => setTimeout(res, 10));
            }
            // removing lock will lead to errors and panics!
            isWorking = true;
            const r = tryAuto();
            if (mode === 'boost') {
                if (r.available) {
                    for (const tac of r.tactic) {
                        await sendTactic(tac);
                    }
                }
            } else {
                setS(r);
            }
            isWorking = false;
        });
    }, [mode]);
    return (
        <button className={css.toolButton} onClick={async () => {
            if (s.available) {
                for (const tac of s.tactic) {
                    await sendTactic(tac);
                }
            } else if (mode === 'boost') {
                setMode('normal');
            } else {
                setMode('boost');
            }
        }}>
            {g`auto_proof`}
            {s.available && <><br /><span className={css.autoProof}>{s.type === 'normal' ? '✓' : '🕮'}</span></>}
            {mode === 'boost' && <><br /><span className={css.autoProof}>{'>>'}</span></>}
        </button>
    );
};

export const Toolbar = () => {
    return (
        <div className={css.toolContain}>
            <ToolButton onClick={newAssert} label={g`new_assertion`} />
            <AutoProofButton />
            <ToolButton onClick={() => {
                const tactic = window.prompt(g`enter_tactic`);
                if (tactic) {
                    sendTactic(tactic);
                }
            }} label={g`custom_tactic`} />
        </div>
    );
};