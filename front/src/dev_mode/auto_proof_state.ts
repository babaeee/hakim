import { useEffect, useState } from "react";

export const getAutoProofState = (): boolean => {
    return (localStorage.getItem("auto_proof_state") !== "off");
};

type EventListener = (s: boolean) => void;

let listeners: EventListener[] = [];

const emit = () => {
    const v = getAutoProofState();
    console.log('Emitted auto proof state', v, ' to ', listeners.length, ' people');
    listeners.forEach((f) => f(v));
};

const subscribe = (f: EventListener) => {
    listeners.push(f);
    emit();
    return () => {
        listeners = listeners.filter((x) => x !== f);
    };
};

export const useAutoProofState = (): boolean => {
    const [s, setS] = useState(getAutoProofState());
    useEffect(() => {
        return subscribe(setS);
    }, []);
    return s;
};

export const setAutoProofState = (s: boolean) => {
    if (s) {
        localStorage.setItem("auto_proof_state", "on");
    } else {
        localStorage.setItem("auto_proof_state", "off");
    }
    emit();
};


