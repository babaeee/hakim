import { Fragment } from "react";
import { useNavigate } from "react-router-dom";
import { allLibraryData, fromMiddleOfLib } from "../../hakim";
import { g } from "../../i18n";
import { openProofSession } from "../root/Root";
import css from "./LibraryViewer.module.css";

export const LibraryViewer = () => {
    const data = allLibraryData();
    const navigator = useNavigate();
    const onFinish = async (lib: string, name: string) => {
        if (await fromMiddleOfLib(lib, name)) {
            openProofSession(navigator, {});
        }
    };
    return (
        <div dir="ltr" className={css.main}>
            <h1 className={css.title}>{g`library`}</h1>
            <p className={css.text} dir="rtl">{g`library_intro`}</p>
            <ul className={css.text}>
                {data.map((x) => (
                    <Fragment key={x.name}>
                        <li>{x.name}</li>
                        <ul>
                            {x.rules.map((y) => (
                                <li key={y.name} onClick={() => onFinish(x.name, y.name)}>
                                    <span className={css[y.kind]}>{y.kind}</span> {y.name}{y.ty && `: ${y.ty}`}
                                </li>
                            ))}
                        </ul>
                    </Fragment>
                ))}
            </ul>
        </div>
    );
};
