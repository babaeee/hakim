import { g } from "../../i18n";
import css from "./Adventure.module.css";
import data from "../../../adventure/root.yml";

export const Adventure = () => {
    return (
        <div className={css.main}>
            <h1 className={css.title}>{g`adventure`}</h1>
            <p className={css.text}>{JSON.stringify(data)}</p>
        </div>
    );
};
