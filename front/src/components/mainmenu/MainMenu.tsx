import { changeLang, g } from "../../i18n";
import { State } from "../root/Root";
import css from "./MainMenu.module.css";

export const MainMenu = ({ onFinish }: { onFinish: (x: State["mode"]) => void }) => {
    return (
        <div className={css.main}>
            <h1 className={css.title}>{g`babaeee_coq`}</h1>
            <ul dir="ltr" className={css.exampleSection}>
                <li onClick={() => onFinish(`adventure`)} className={css.exampleItem}>{g`adventure`}</li>
                <li onClick={() => onFinish(`sandbox`)} className={css.exampleItem}>{g`sandbox`}</li>
                <li onClick={() => onFinish(`library`)} className={css.exampleItem}>{g`library`}</li>
                <li onClick={changeLang} className={css.exampleItem}>{g`change_lang`}</li>
            </ul>
        </div>
    );
};
