import { Instance } from "../../../hakim-wasm/pkg/hakim_wasm";

declare let window: Window & {
    ask_question: (q: string) => string;
    panic_handler: (s: string) => void;
};

window.ask_question = (x) => {
    return window.prompt(x) || '';
};
window.panic_handler = (x) => {
    document.body.innerHTML = `<pre>${x}</pre>`;
};


const instance = new Instance();
instance.load_library('Arith');
instance.load_library('Eq');
instance.load_library('Logic');
instance.load_library('Induction');
instance.load_library('Sigma');

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
    return { history, monitor: monitor.Monitor, isFinished: false };
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

const checkError = (error?: string) => {
    if (error) {
        alert(error);
        return false;
    }
    return true;
};

const checkErrorAndUpdate = (error?: string) => {
    if (checkError(error)) {
        emit();
        return true;
    }
    return false;
};

export const sendTactic = (tactic: string) => {
    console.log(`tactic: `, tactic);
    return checkErrorAndUpdate(instance.run_tactic(tactic));
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

export const setGoal = (goal: string) => {
    return checkErrorAndUpdate(instance.start_session(goal));
};

export const runSuggMenuHyp = (hypName: string, sugg: string) => {
    return checkErrorAndUpdate(instance.run_suggest_menu_hyp(hypName, sugg));
};

export const runSuggDblGoal = () => {
    return checkErrorAndUpdate(instance.suggest_dblclk_goal());
};

export const runSuggDblHyp = (hyp: string) => {
    return checkErrorAndUpdate(instance.suggest_dblclk_hyp(hyp));
};

export const suggMenuHyp = (hypName: string) => {
    const suggs = instance.suggest_menu_hyp(hypName);
    if (!suggs) return [];
    return suggs.split(',').filter((x) => x !== '');
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
