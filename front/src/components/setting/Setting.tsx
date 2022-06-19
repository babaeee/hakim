import { getDevState, setDevState, useDevState } from "../../dev_mode";
import { changeLang, g, getLang } from "../../i18n";

export const Setting = () => {
    const changeDevMode = () => {
        if (getDevState() === 'off') {
            setDevState('ready');
        } else {
            setDevState('off');
        }
    };
    const devState = useDevState();
    return <div style={{ color: 'white', width: '100%' }} dir="ltr">
        <ul>
            <li>{g`change_lang`} <button onClick={changeLang}>{getLang()}</button></li>
            <li>{g`dev_mode`} <button onClick={changeDevMode}>{devState === 'off' ? 'off' : 'on'}</button></li>
        </ul>
    </div>;
};