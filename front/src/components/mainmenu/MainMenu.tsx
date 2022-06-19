import { g } from "../../i18n";
import css from "./MainMenu.module.css";
import { Link } from "react-router-dom";
import { Title } from "../util/Title";

export const MainMenu = () => {
    return (
        <div className={css.main}>
            <Title title={g`main_menu`} />
            <h1 className={css.title}>{g`babaeee_coq`}</h1>
            <ul dir="ltr" className={css.exampleSection}>
                <Link to={`/adventure`} className={css.exampleItem}>{g`adventure`}</Link>
                <Link to={`/sandbox`} className={css.exampleItem}>{g`sandbox`}</Link>
                <Link to={`/library`} className={css.exampleItem}>{g`library`}</Link>
                <Link to={`/setting`} className={css.exampleItem}>{g`setting`}</Link>
            </ul>
        </div>
    );
};
