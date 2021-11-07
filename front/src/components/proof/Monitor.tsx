import { useEffect, useState } from "react";
import { runSuggDblGoal, runSuggMenuHyp, sendTactic, State, subscribe, suggMenuHyp } from "../../hakim";
import css from "./monitor.module.css";
import { useMenuState, ControlledMenu, MenuItem } from "@szhsin/react-menu";
import '@szhsin/react-menu/dist/index.css';
import { g } from "../../i18n";

const Hyp = ({ name, ty }: { name: string, ty: string }): JSX.Element => {
    const { toggleMenu, ...menuProps } = useMenuState();
    const [anchorPoint, setAnchorPoint] = useState({ x: 0, y: 0 });
    const [suggs, setSuggs] = useState([] as string[]);
    return (
        <div onContextMenu={e => {
            e.preventDefault();
            setSuggs(suggMenuHyp(name));
            setAnchorPoint({ x: e.clientX, y: e.clientY });
            toggleMenu(true);
        }}>
            {name}: {ty}
            <ControlledMenu {...menuProps} anchorPoint={anchorPoint}
                onClose={() => toggleMenu(false)}>
                {suggs.map((x) => <MenuItem onClick={() => runSuggMenuHyp(name, x)}>{x}</MenuItem>)}
            </ControlledMenu>
        </div>
    );
};

type MonitorProps = {
    onFinish: () => void;
};

export const Monitor = ({ onFinish }: MonitorProps) => {
    const [s, setS] = useState(undefined as State | undefined);
    useEffect(() => {
        return subscribe((newS) => {
            setS(newS);
        })
    }, []);
    if (!s) {
        return <div className={css.monitor}>Loading...</div>;
    }
    if (s.isFinished) {
        return <div className={css.monitor}>
            {g`no_more_subgoal`}
            <button onClick={onFinish}>{g`exit`}</button>
        </div>;
    }
    const { hyps, goals } = s.monitor;
    return (
        <div className={css.monitor} dir="ltr">
            {hyps.map(([name, ty]: any) => (
                <Hyp name={name} ty={ty} />
            ))}
            {[...goals].reverse().map((goal: any) => (
                <><hr /><div onDoubleClick={() => runSuggDblGoal()}>{goal}</div></>
            ))}
        </div>
    )
};