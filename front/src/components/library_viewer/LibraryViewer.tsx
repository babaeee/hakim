import React, { useEffect, useState } from "react";
import { Link, useNavigate } from "react-router-dom";
import { allLibraryData, fromMiddleOfLib, LibraryItemKind, LibraryData } from "../../hakim";
import { g } from "../../i18n";
import { openProofSession } from "../root/Root";
import { Title } from "../util/Title";
import css from "./LibraryViewer.module.css";

const Collapsable: React.FC<{ name: string, children: any }> = ({ name, children }) => {
    const [collapsed, setCollapse] = useState(true);
    return <>
        <div onClick={() => setCollapse(!collapsed)}>{name}</div>
        {!collapsed && <div>{children}</div>}
    </>;
};

export const LibraryViewer = () => {
    const [data, setData] = useState("loading" as ("loading" | LibraryData[]));
    const navigator = useNavigate();
    const onFinish = async (lib: string, name: string, kind: LibraryItemKind) => {
        alert('Im broken');
        // if (await fromMiddleOfLib(lib, name, kind)) {
        //     openProofSession(navigator, {});
        // }
    };
    useEffect(() => {
        (async () => {
            setData(await allLibraryData());
        })();
    }, []);
    if (data === "loading") {
        return <div>loading</div>
    }
    return (
        <div dir="ltr" className={css.main}>
            <Title title={g`library`} />
            <h1 className={css.title}>{g`library`}</h1>
            <p className={css.text} dir="rtl">{g`library_intro`}</p>
            <p><Link to="notation">{g`notations`}</Link></p>
            <ul className={css.text}>
                {data.map((x) => (
                    <Collapsable key={x.name} name={x.name}>
                        {x.rules.filter((x) => x.kind !== 'Suggestion').map((y) => (
                            <li key={y.name} onClick={() => onFinish(x.name, y.name, y.kind)}>
                                <span className={css[y.kind]}>{y.kind}</span> {y.name}{y.ty && `: ${y.ty}`}
                            </li>
                        ))}
                    </Collapsable>
                ))}
            </ul>
        </div>
    );
};
