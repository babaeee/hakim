import classNames from "classnames";
import { useState } from "react";
import { getText } from "../../../i18n"
import { Monitor } from "./Monitor";
import { Search } from "./Search";

import css from "./Tabs.module.css";

const tabComponents = {
    proof_screen: Monitor,
    search: Search,
};

type tabName = 'proof_screen' | 'search';

const tabs: tabName[] = [
    'proof_screen', 'search',
];

export const Tabs = () => {
    const [ct, setCt] = useState(tabs[0]);
    const Comp = tabComponents[ct];
    return (
        <div className={css.root}>
            <div className={css.tabs}>
                {tabs.map((x) => <button
                    key={x}
                    onClick={() => setCt(x)}
                    className={classNames({ [css.tab]: true, [css.selected]: x === ct })}
                >{getText(x)}</button>)}
            </div>
            <div className={css.body}>
                <Comp />
            </div>
        </div>
    )
};
