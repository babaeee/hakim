import { useState } from "react"
import { searchPattern, SearchResult } from "../../../hakim";
import { g } from "../../../i18n";


export const Search = () => {
    const [value, setValue] = useState('');
    const [searchResult, setSearchResult] = useState([] as SearchResult[]);
    return (
        <div dir="ltr">
            <input type="text" onChange={(e) => setValue(e.target.value)} />
            <button onClick={() => {
                const r = searchPattern(value);
                setSearchResult(r);
            }}>{g`submit`}</button>
            <div>
                {searchResult.map(({ name, ty }) => <div onClick={() => alert(name)}>{name}: {ty}</div>)}
            </div>
        </div>
    )
}