import { Instance } from "../../../hakim-wasm/pkg/hakim_wasm";
import { normalPrompt } from "../dialog";
import { fromRust } from "../i18n";

declare let window: Window & {
    ask_question: (q: string) => Promise<string>;
    panic_handler: (s: string) => void;
    instance: Instance;
    hardReset: () => void;
};

window.ask_question = (x) => {
    return normalPrompt(fromRust(x));
};
window.panic_handler = (x) => {
    document.body.innerHTML = `<pre>${x}</pre>`;
};


const checkError = (error?: string) => {
    if (error) {
        alert(error);
        return false;
    }
    return true;
};

const instance = new Instance();

window.instance = instance;

const hardReset = () => {
    localStorage.clear();
    window.onbeforeunload = null;
    window.location.reload();
};

window.hardReset = hardReset;

const prevBackup = localStorage.getItem('wasmState');

if (prevBackup) {
    if (!instance.from_backup(JSON.parse(prevBackup))) {
        window.alert('backup version is incompatible. reloading...');
        hardReset();
    }
}

export const toBackup = () => {
    return JSON.stringify(instance.to_backup());
};

export type State = {
    history: string[],
} & ({ isFinished: true } | {
    isFinished: false
    monitor: {
        hyps: string[],
        goals: string[],
    },
});

type EventListener = (s: State) => void;

let listeners: EventListener[] = [];

const calcState = (): State => {
    const history = instance.get_history();
    console.log(instance.monitor());
    const monitor = instance.monitor();
    if (monitor === 'Finished') {
        return { history, isFinished: true };
    }
    return { history, monitor: monitor.Running, isFinished: false };
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

export const sendTactic = (tactic: string) => {
    console.log(`tactic: `, tactic);
    return checkErrorAndUpdate(() => instance.run_tactic(tactic));
};

export const tryTactic = (tactic: string): boolean => {
    return instance.try_tactic(tactic);
}

export type SearchResult = {
    name: string,
    ty: string,
};

export const searchPattern = (expr: string): SearchResult[] => {
    return instance.search(expr).split('\n').filter((x) => x.trim() !== '').map((x) => {
        let y = x.split(': ');
        return {
            name: y[0],
            ty: y.slice(1).join(': '),
        };
    });
};

export const setGoal = (goal: string, libs: string = 'All') => {
    localStorage.setItem('last_goal', `Goal (${goal})`);
    return checkErrorAndUpdate(() => Promise.resolve(instance.start_session(goal, libs)));
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
    tactic: string,
};

export const tryAuto = (): TryAutoResult => {
    const tactic = instance.try_auto();
    if (tactic) {
        return {
            available: true,
            tactic,
        };
    }
    return { available: false };
};

type LibraryData = {
    name: string,
    rules: {
        kind: 'Import' | 'Axiom',
        name: string,
        ty?: string,
    }[],
};

export const fromMiddleOfLib = (lib: string, name: string) => {
    return checkErrorAndUpdate(() => Promise.resolve(instance.start_session_from_lib(lib, name)));
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
