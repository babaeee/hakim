import { useEffect, useState } from "react";
import { State, subscribe } from "../../hakim";
import css from "./monitor.module.css";

export const Monitor = () => {
    const [s, setS] = useState(undefined as State | undefined);
    useEffect(() => {
        return subscribe((newS) => {
            setS(newS);
        })
    }, []);
    return (
        <div className={css.monitor}>
            {JSON.stringify(s)}
        </div>
    )
};