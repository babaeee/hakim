import { Instance } from "../../../hakim-wasm/pkg/hakim_wasm";
import { normalPrompt } from "../dialog";
import { fromRust, g } from "../i18n";
import { loadLibText } from "./lib_text";

declare let window: Window & {
    ask_question: (q: string) => Promise<string>;
    panic_handler: (s: string) => void;
    load_lib_json: (s: string) => object;
    instance: Instance;
    hardReset: () => void;
};

window.ask_question = (x) => {
    return normalPrompt(fromRust(x));
};
window.panic_handler = (x) => {
    document.body.innerHTML = `<pre>${x}</pre>`;
};
window.load_lib_json = loadLibText;

const checkError = (error?: string) => {
    if (error) {
        alert(error);
        return false;
    }
    return true;
};

const instance = new Instance();

window.instance = instance;

const wasmReset = () => {
    localStorage.removeItem('wasmState');
    window.onbeforeunload = null;
    window.location.reload();
};

window.hardReset = wasmReset;

const prevBackup = localStorage.getItem('wasmState');

if (prevBackup) {
    if (!instance.from_backup(JSON.parse(prevBackup))) {
        window.alert('backup version is incompatible. reloading...');
        wasmReset();
    }
}

export const toBackup = () => {
    return JSON.stringify(instance.to_backup());
};

export type State = {
    undoHistory: string[],
    redoHistory: string[],
} & ({ isFinished: true } | {
    isFinished: false
    monitor: {
        hyps: string[],
        goals: string[],
    },
});

type EventListener = (s: State) => void;

let listeners: EventListener[] = [];

const isState = (x: State): x is State => {
    if (!(x.undoHistory instanceof Array) || !(x.redoHistory instanceof Array)) {
        console.log('state does not have history\nState: ' + JSON.stringify(x));
        return false;
    }
    if (x.isFinished === true) return true;
    if (x.isFinished !== false) return false;
    if (!x.monitor) return false;
    if (!(x.monitor.goals instanceof Array)) return false;
    if (!(x.monitor.hyps instanceof Array)) return false;
    return true;
};

const calcState = (): State => {
    const f = (): State => {
        const [undoHistory, redoHistory] = instance.get_history() || [[], []];
        console.log(instance.monitor());
        const monitor = instance.monitor();
        if (monitor === 'Finished') {
            return { undoHistory, redoHistory, isFinished: true };
        }
        return { undoHistory, redoHistory, monitor: monitor.Running, isFinished: false };
    };
    const r = f();
    if (!isState(r)) {
        if (localStorage.getItem('wasmState') === null) {
            throw new Error('invalid state');
        }
        window.onbeforeunload = null;
        localStorage.removeItem('wasmState');
        localStorage.removeItem('reactState');
        window.location.reload();
    }
    return r;
};

export const emit = () => {
    const v = calcState();
    console.log('Emitted ', v, ' to ', listeners.length, ' people');
    listeners.forEach((f) => f(v));
};

export const subscribe = (f: EventListener) => {
    listeners.push(f);
    emit();
    return () => {
        listeners = listeners.filter((x) => x !== f);
    };
};

const checkErrorAndUpdate = async (error: () => Promise<string | undefined>) => {
    if (checkError(await error())) {
        emit();
        return true;
    }
    return false;
};

export const getActionHint = (tactic: string) => {
    return instance.action_of_tactic(tactic);
}

export const sendTactic = (tactic: string) => {
    console.log(`tactic: `, tactic);
    return checkErrorAndUpdate(() => instance.run_tactic(tactic));
};

export const notationList = (): string[] => {
    return instance.notation_list();
};

export const getNatural = (): string => {
    return fromRust(instance.natural() || '$invalid_state');
};

export const tryTactic = (tactic: string): boolean => {
    return instance.try_tactic(tactic);
};

export const check = (query: string): string => {
    return instance.check(query);
};

export type SearchResult = {
    name: string,
    ty: string,
};

export const searchPattern = (expr: string): SearchResult[] => {
    const r = instance.search(expr);
    return r.map(([a, b]: [string, string]) => {
        return {
            name: a,
            ty: b,
        };
    });
};

export const setGoal = (goal: string, libs: string = '/', params: string = '') => {
    localStorage.setItem('last_goal', `Goal (${goal})`);
    return checkErrorAndUpdate(() => Promise.resolve(instance.start_session(goal, libs, params)));
};

export const runSuggMenuHyp = (hypName: string, i: number) => {
    return checkErrorAndUpdate(() => instance.run_suggest_menu_hyp(hypName, i));
};

export const runSuggMenuGoal = (i: number) => {
    return checkErrorAndUpdate(() => instance.run_suggest_menu_goal(i));
};

export const runSuggDblGoal = () => {
    return checkErrorAndUpdate(() => instance.suggest_dblclk_goal());
};

export const runSuggDblHyp = (hyp: string) => {
    return checkErrorAndUpdate(() => instance.suggest_dblclk_hyp(hyp));
};

export const spanPosOfHyp = (hyp: string, l: number, r: number): number | undefined => {
    const x = instance.pos_of_span_hyp(hyp, l, r);
    return x;
};
export const spanPosOfGoal = (l: number, r: number): number | undefined => {
    const x = instance.pos_of_span_goal(l, r);
    return x;
};

const parenSplit = (txt: string): string[] => {
    const r = [];
    let cur = "";
    let depth = 0;
    for (const c of txt) {
        if (c === '(') {
            depth += 1;
            if (depth === 1) continue;
        }
        if (c === ')') {
            depth -= 1;
            if (depth === 0) {
                r.push(cur);
                cur = "";
            }
        }
        if (depth > 0) {
            cur += c;
        }
    }
    return r.map((x) => fromRust(x));
}

export const suggMenuHyp = (hypName: string) => {
    const suggs = instance.suggest_menu_hyp(hypName);
    if (!suggs) return [];
    return parenSplit(suggs).map((x, i) => ({
        label: x,
        action: () => runSuggMenuHyp(hypName, i),
    }));
};

export const suggMenuGoal = () => {
    const suggs = instance.suggest_menu_goal();
    if (!suggs) return [];
    return parenSplit(suggs).map((x, i) => ({
        label: x,
        action: () => runSuggMenuGoal(i),
    }));
};

export type TryAutoResult = {
    available: false,
} | {
    available: true,
    type: "normal" | "history",
    tactic: string[],
};

export const tryAuto = (): TryAutoResult => {
    const tactic = instance.try_auto();
    if (tactic) {
        return {
            available: true,
            type: "normal",
            tactic: [tactic],
        };
    }
    const history_tactics = instance.try_auto_history();
    if (history_tactics) {
        return {
            available: true,
            type: "history",
            tactic: history_tactics,
        };
    }
    return { available: false };
};

export type LibraryItemKind = 'Import' | 'Axiom' | 'Suggestion' | 'Theorem';

type LibraryData = {
    name: string,
    rules: {
        kind: LibraryItemKind,
        name: string,
        ty?: string,
    }[],
};

export const fromMiddleOfLib = (lib: string, name: string, kind: LibraryItemKind) => {
    return checkErrorAndUpdate(() => Promise.resolve(instance.start_session_from_lib(lib, name, kind === 'Theorem')));
};

export const allLibraryData = (): LibraryData[] => {
    const x = instance.all_library_data();
    const convertRule = (r: any) => {
        const kind = Object.keys(r)[0];
        return {
            kind,
            ...r[kind],
        };
    };
    return Object.keys(x).map((a) => ({ name: a, rules: x[a].map(convertRule) }));
};
