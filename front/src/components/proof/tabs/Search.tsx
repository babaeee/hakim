import { useContext, useState } from "react"
import { searchPattern, SearchResult } from "../../../hakim";
import { g } from "../../../i18n";
import { UnicodeHelp } from "../../unicode/UnicodeHelp";
import { UnicodeInput } from "../../unicode/UnicodeInput";
import { ProofContext } from "../Proof";
import css from "./Search.module.css";

export const Search = () => {
    const [value, setValue] = useState('');
    const [help, setHelp] = useState(false);
    const [searchResult, setSearchResult] = useState([] as SearchResult[]);
    const { appendLemma } = useContext(ProofContext);
    const work = () => {
        const r = searchPattern(value);
        setSearchResult(r);
    };
    return (
        <div dir="ltr">
            <UnicodeInput value={value} onChange={setValue} enableHelp={setHelp} onEnter={work} />
            <button onClick={work}>{g`submit`}</button>
            {help && <div className={css.searchResult}>
                <UnicodeHelp />
            </div>}
            {!help && <div className={css.searchResult}>
                {searchResult.map(({ name, ty }) => <div key={name} onClick={() => appendLemma(name)}>{name}: {ty}</div>)}
            </div>}
        </div>
    )
}