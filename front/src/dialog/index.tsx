import ReactDOM from "react-dom";
import css from "./dialog.module.css";
import { NormalPrompt } from "./Prompt";

export const normalPrompt = (msg: string, defaultValue: string = ""): Promise<string> => {
    const div = document.createElement('div');
    div.className = css.root;
    document.body.appendChild(div);
    return new Promise((res) => {
        ReactDOM.render(<NormalPrompt msg={msg} defaultValue={defaultValue} onDone={(result) => {
            document.body.removeChild(div);
            res(result);
        }} />, div);
    });
};
