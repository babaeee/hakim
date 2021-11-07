import { useState } from "react";
import { g } from "../../i18n";

type SanboxProps = {
    onFinish: (goal: string) => void,
};

export const Sandbox = ({ onFinish }: SanboxProps) => {
    const [text, setText] = useState("");
    return (
        <div>
            <h1>{g`sandbox_title`}</h1>
            <input type="text" onChange={(ev) => setText(ev.target.value)} value={text} />
            <button onClick={() => onFinish(text)}>{g`submit`}</button>
        </div>
    );
};
