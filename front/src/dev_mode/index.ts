import { useEffect, useState } from "react";

export type DevState = "off" | "ready" | "admin" | "debug";

export const getDevState = (): DevState => {
    return (localStorage.getItem("dev_state") || "off") as DevState;
};

type EventListener = (s: DevState) => void;

let listeners: EventListener[] = [];

const emit = () => {
    const v = getDevState();
    console.log('Emitted dev state', v, ' to ', listeners.length, ' people');
    listeners.forEach((f) => f(v));
};

const subscribe = (f: EventListener) => {
    listeners.push(f);
    emit();
    return () => {
        listeners = listeners.filter((x) => x !== f);
    };
};

export const useDevState = (): DevState => {
    const [s, setS] = useState(getDevState());
    useEffect(() => {
        return subscribe(setS);
    }, []);
    return s;
};

export const setDevState = (s: DevState) => {
    localStorage.setItem("dev_state", s);
    emit();
};

export const isDebug = (): boolean => {
    return getDevState() === 'debug';
};

