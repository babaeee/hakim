import { convertTable } from "./table";

type Props = {
    value: string,
    onChange: (x: string) => any,
    onEnter: () => any,
    enableHelp: (x: boolean) => any,
};

const transform = (s: string | undefined) => {
    if (!s) return '';
    for (const [ascii, unicode] of convertTable) {
        if (s.endsWith(`;${ascii};`)) {
            return s.slice(0, -ascii.length - 2) + unicode;
        }
    }
    return s;
}

export const UnicodeInput = ({ value, onChange, enableHelp, onEnter }: Props) => {
    return (
        <input type="text" value={value} onChange={(e) => {
            const txt = transform(e.target.value);
            enableHelp(txt.endsWith(';'));
            onChange(txt);
        }} onKeyPress={(e) => {
            if (e.code === 'Enter') {
                onEnter();
            }
        }} />
    );
};
