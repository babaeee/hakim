import { Fragment } from "react";
import { convertTable } from "./table";
import css from "./unicode.module.css";

export const UnicodeHelp = () => {
    return (
        <Fragment>
            {convertTable.map(([a, b]) => <Fragment key={a}><span dir="ltr" className={css.helpItem}>{`;${a}; = ${b}`}</span> </Fragment>)}
        </Fragment>
    );
};
