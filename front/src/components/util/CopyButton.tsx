import { useState } from "react";
import { g } from "../../i18n";
import { delay } from "../../util";

type CopyButtonProps = {
    text: () => string,
    label: string,
};

export const CopyButton = ({ text, label }: CopyButtonProps) => {
    const [isCopied, setCopied] = useState(false);
    if (isCopied) {
        return <button>{g`copied_in_clipboard`}</button>;
    }
    const work = async () => {
        await navigator.clipboard.writeText(text());
        setCopied(true);
        await delay(1000);
        setCopied(false);
    };
    return (
        <button onClick={work}>{label}</button>
    );
};
