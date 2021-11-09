import { useContext, useState } from "react"
import { searchPattern, SearchResult } from "../../../hakim";
import { g } from "../../../i18n";
import { ProofContext } from "../Proof";
import css from "./Search.module.css";

export const Search = () => {
    const [value, setValue] = useState('');
    const [searchResult, setSearchResult] = useState([] as SearchResult[]);
    const { appendLemma } = useContext(ProofContext);
    return (
        <div dir="ltr">
            <input type="text" onChange={(e) => setValue(e.target.value)} />
            <button onClick={() => {
                const r = searchPattern(value);
                setSearchResult(r);
            }}>{g`submit`}</button>
            <div className={css.searchResult}>
                {searchResult.map(({ name, ty }) => <div key={name} onClick={() => appendLemma(name)}>{name}: {ty}</div>)}
            </div>
        </div>
    )
}