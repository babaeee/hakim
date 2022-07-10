import { useEffect, useState } from "react";
import { normalPrompt } from "../../dialog";
import { sendTactic, subscribe, tryAuto, TryAutoResult } from "../../hakim";
import { g } from "../../i18n";
import css from "./toolbar.module.css";
import logo from "../../logo.png"
import { flip, offset, shift, useFloating } from '@floating-ui/react-dom';

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
    const { x, y, reference, floating, strategy } = useFloating({
        middleware: [
            offset(6),
            flip(),
            shift({ padding: 5 }),
        ],
        placement: 'left',
    });
    const [hover, setHover] = useState(false);
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
    const showTurboTooltip = hover && mode === 'boost';
    return (
        <>
            <button ref={reference} className={css.toolButton}
                onMouseEnter={() => setHover(true)}
                onMouseLeave={() => setHover(false)}
                onClick={async () => {
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
            {showTurboTooltip && <div
                ref={floating}
                style={{
                    position: strategy,
                    top: y ?? 0,
                    left: x ?? 0,
                }}
                className={css.tooltip}
            >
                {g`auto_proof_turbo_tooltip`}
            </div>}
        </>
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
            <div className={css.footer}>
                <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
                    <path fillRule="evenodd" d="M12.316 3.051a1 1 0 01.633 1.265l-4 12a1 1 0 11-1.898-.632l4-12a1 1 0 011.265-.633zM5.707 6.293a1 1 0 010 1.414L3.414 10l2.293 2.293a1 1 0 11-1.414 1.414l-3-3a1 1 0 010-1.414l3-3a1 1 0 011.414 0zm8.586 0a1 1 0 011.414 0l3 3a1 1 0 010 1.414l-3 3a1 1 0 11-1.414-1.414L16.586 10l-2.293-2.293a1 1 0 010-1.414z" clipRule="evenodd" />
                </svg>
                with
                <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
                    <path fillRule="evenodd" d="M3.172 5.172a4 4 0 015.656 0L10 6.343l1.172-1.171a4 4 0 115.656 5.656L10 17.657l-6.828-6.829a4 4 0 010-5.656z" clipRule="evenodd" />
                </svg>
                by
                <img src={logo} alt="babaeee logo" />
            </div>
        </div>
    );
};
