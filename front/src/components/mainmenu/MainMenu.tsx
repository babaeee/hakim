import { g } from "../../i18n";
import { State } from "../root/Root";
import css from "./MainMenu.module.css";

export const MainMenu = ({ onFinish }: { onFinish: (x: State["mode"]) => void }) => {
    return (
        <div className={css.main}>
            <ul dir="ltr" className={css.exampleSection}>
                <li onClick={() => onFinish(`sandbox`)} className={css.exampleItem}>{g`sandbox`}</li>
            </ul>
        </div>
    );
};
