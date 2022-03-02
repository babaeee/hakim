import { Fragment } from "react";
import { allLibraryData } from "../../hakim";
import { g } from "../../i18n";
import css from "./LibraryViewer.module.css";

export const LibraryViewer = ({ onFinish }: { onFinish: (lib: string, name: string) => void }) => {
    const data = allLibraryData();
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
