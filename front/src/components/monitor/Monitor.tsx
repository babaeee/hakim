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
    if (!s) {
        return <div>Loading...</div>;
    }
    const { hyps, goals } = s.monitor;
    return (
        <div className={css.monitor} dir="ltr">
            {hyps.map(([name, ty]: any) => (
                <div>{name}: {ty}</div>
            ))}
            {[...goals].reverse().map((goal: any) => (
                <><hr /><div>{goal}</div></>
            ))}
        </div>
    )
};