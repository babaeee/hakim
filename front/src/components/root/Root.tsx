import { toBackup } from "../../hakim";
import { isRTL } from "../../i18n";
import { Adventure } from "../adventure/Adventure";
import { LibraryViewer } from "../library_viewer/LibraryViewer";
import { MainMenu } from "../mainmenu/MainMenu";
import { Proof } from "../proof/Proof";
import { Sandbox } from "../sandbox/Sandbox";
import { BrowserRouter, NavigateFunction, Route, Routes } from "react-router-dom";
import css from "./Root.module.css";
import { addToWinList } from "../adventure/winList";

export type State = {
    mode: 'sandbox' | 'proof' | 'mainmenu' | 'library' | 'adventure',
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

let todoAfterProof: AfterProof = {};

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
    runProofAction(navigate, todoAfterProof.onSolve || { type: 'back' });
};

export const cancelProof = (navigate: NavigateFunction) => {
    runProofAction(navigate, todoAfterProof.onCancel || { type: 'back' });
};

export const openProofSession = (navigate: NavigateFunction, afterProof: AfterProof) => {
    todoAfterProof = afterProof;
    navigate('/proof');
};

export const Root = () => {
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
                        <Route path="library" element={<LibraryViewer />} />
                        <Route path="*" element={<div>404 not found</div>} />
                    </Route>
                </Routes>
            </BrowserRouter>
        </div>
    );;
};
