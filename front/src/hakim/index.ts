import { Instance } from "../../../hakim-wasm/pkg/hakim_wasm";

const instance = new Instance();
instance.load_library('Arith');
instance.start_session('2 = 3');

export type State = {
    history: string[],
    monitor: {
        hyps: string[],
        goals: string[],
    },
};

type EventListener = (s: State) => void;

let listeners: EventListener[] = [];

export const emit = () => {
    const history = instance.get_history();
    const monitor = instance.monitor().Monitor;
    const v = { history, monitor };
    listeners.forEach((f) => f(v));
};

export const subscribe = (f: EventListener) => {
    listeners.push(f);
    emit();
    return () => {
        listeners = listeners.filter((x) => x !== f);
    };
};

const checkErrorAndUpdate = (error?: string) => {
    if (error) {
        alert(error);
        return;
    }
    emit();
};

export const sendTactic = (tactic: string) => {
    checkErrorAndUpdate(instance.run_tactic(tactic));
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
