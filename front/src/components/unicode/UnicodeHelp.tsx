import { Fragment } from "react";
import { convertTable } from "./table";
import css from "./unicode.module.css";

export const UnicodeHelp = () => {
    return (
        <Fragment>
            <div className={css.helpContainer}>
                {convertTable.map(([a, b]) =>
                    <Fragment key={a}>
                        <span dir="ltr" className={css.helpItem}>
                            <span>
                                ;{a};
                            </span>
                            <span style={{color: "var(--gray-2)", padding: "0 5px"}}>
                                =
                            </span>
                            <span style={{color: "var(--primary)"}}>
                                {b}
                            </span>
                        </span>
                    </Fragment>
                )}
            </div>
        </Fragment>
    );
};
