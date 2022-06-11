import { notationList } from "../../hakim";

const list = notationList();

export const NotationHelper = () => {
    return <div style={{ color: 'white', width: '100%' }} dir="ltr">
        <ul>
            {list.map((x) => <li key={x}>{x}</li>)}
        </ul>
    </div>;
};