import { setDevState, useDevState } from "./index";
import css from "./DevStateComponent.module.css";

export const DevStateComponent = () => {
    const devState = useDevState();
    if (devState === 'off') {
        return <></>;
    }
    const shuffleDevState: React.MouseEventHandler<HTMLDivElement> = (e) => {
        e.stopPropagation();
        if (devState === 'ready') {
            setDevState('admin');
        }
        if (devState === 'admin') {
            setDevState('debug');
        }
        if (devState === 'debug') {
            setDevState('ready');
        }
    };
    return <div onClick={shuffleDevState} className={css.main}>{devState[0]}</div>;
};
