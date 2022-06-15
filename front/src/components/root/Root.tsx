import { toBackup } from "../../hakim";
import { g, isRTL } from "../../i18n";
import { Adventure } from "../adventure/Adventure";
import { LibraryViewer } from "../library_viewer/LibraryViewer";
import { MainMenu } from "../mainmenu/MainMenu";
import { Proof } from "../proof/Proof";
import { Sandbox } from "../sandbox/Sandbox";
import { BrowserRouter, NavigateFunction, Route, Routes } from "react-router-dom";
import css from "./Root.module.css";
import { addToWinList } from "../adventure/winList";
import { useState } from "react";
import { NotationHelper } from "../notation/NotationHelper";

export type State = {
    proofState: ProofState,
};

const storedState = (): State => {
    const json = localStorage.getItem('reactState');
    if (json) {
        return JSON.parse(json);
    } else {
        return {
            proofState: {
                afterProof: {},
                suggestedLemmas: [],
                text: "",
            }
        };
    }
};

let stateToStore: State = storedState();

window.onbeforeunload = () => {
    localStorage.setItem('reactState', JSON.stringify(stateToStore));
    localStorage.setItem('wasmState', toBackup());
};

export type AfterProofAction = {
    type: "back"
} | {
    type: "goto",
    url: string,
} | {
    type: "win",
    level: string,
    then: AfterProofAction,
};

type AfterProof = {
    onSolve?: AfterProofAction | undefined,
    onCancel?: AfterProofAction | undefined,
};

type ProofState = {
    afterProof: AfterProof,
    suggestedLemmas: string[],
    text: string,
};

export let proofState: ProofState = stateToStore.proofState;

const runProofAction = (navigate: NavigateFunction, action: AfterProofAction) => {
    if (action.type === 'back') {
        window.history.back();
        return;
    }
    if (action.type === 'goto') {
        navigate(action.url, { replace: true });
        return;
    }
    addToWinList(action.level);
    runProofAction(navigate, action.then);
};

export const solveProof = (navigate: NavigateFunction) => {
    runProofAction(navigate, proofState.afterProof.onSolve || { type: 'back' });
};

export const cancelProof = (navigate: NavigateFunction) => {
    runProofAction(navigate, proofState.afterProof.onCancel || { type: 'back' });
};

type OpenProofOptions = {
    replace?: boolean,
    afterProof?: AfterProof,
    text?: string,
    suggestedLemmas?: string[] | undefined,
};

export const openProofSession = (navigate: NavigateFunction, options: OpenProofOptions = {}) => {
    const afterProof = options.afterProof || {};
    const text = options.text || "";
    const replace = options.replace || false;
    const suggestedLemmas = options.suggestedLemmas || [];
    proofState = { afterProof, text, suggestedLemmas };
    stateToStore.proofState = proofState;
    navigate('/proof', { replace });
};

export const Root = () => {
    const [width, setWidth] = useState(document.documentElement.clientWidth);
    const [height, setheight] = useState(document.documentElement.clientHeight);
    window.onresize = () => {
        setWidth(document.documentElement.clientWidth);
        setheight(document.documentElement.clientHeight);
    };
    if (height > width) {
        return (
            <div dir={isRTL() ? 'rtl' : 'ltr'} className={css.mobile}>
                {g`this_page_is_not_optimized_for_mobile`}
            </div>
        )
    }
    return (
        <div dir={isRTL() ? 'rtl' : 'ltr'} className={css.main}>
            <BrowserRouter>
                <Routes>
                    <Route path="/">
                        <Route index element={<MainMenu />} />
                        <Route path="adventure" element={<Adventure />} />
                        <Route path="adventure/*" element={<Adventure />} />
                        <Route path="sandbox" element={<Sandbox />} />
                        <Route path="proof" element={<Proof />} />
                        <Route path="library">
                            <Route index element={<LibraryViewer />} />
                            <Route path="notation" element={<NotationHelper />} />
                        </Route>
                        <Route path="*" element={<div>404 not found</div>} />
                    </Route>
                </Routes>
            </BrowserRouter>
        </div>
    );;
};
