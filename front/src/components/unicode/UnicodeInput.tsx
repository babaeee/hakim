import { useEffect, useRef, useState } from "react";
import { convertTable } from "./table";

type Props = {
    value: string,
    onChange: (x: string) => any,
    onEnter?: () => any,
    enableHelp: (x: boolean) => any,
    className?: string,
    autoFocus?: boolean,
    style?: React.CSSProperties,
};

const transform = (
    s: string | undefined, l: number | null, r: number | null, setCursor: (p: number) => any,
) => {
    if (!s) return;
    if (l === null || r === null) return;
    if (l !== r) return;
    for (const [ascii, unicode] of convertTable) {
        if (s.slice(0, l).endsWith(`;${ascii};`)) {
            setCursor(l - ascii.length - 2 + unicode.length);
            return s.slice(0, l - ascii.length - 2) + unicode + s.slice(l);
        }
    }
    return s;
}

export const UnicodeInput: React.FC<Props> = ({
    autoFocus, value, onChange, enableHelp, onEnter, className, style,
}) => {
    const oe = onEnter || (() => { });
    const [cursor, setCursor]: any = useState(null);
    const ref: any = useRef(null);
    useEffect(() => {
        const input = ref.current;
        if (input) input.setSelectionRange(cursor, cursor);
    }, [ref, cursor, value]);
    return (
        <input ref={ref} style={style} autoFocus={autoFocus} dir="ltr" className={className} type="text"
            onFocus={(e) => e.target.select()}
            value={value} onChange={(e) => {
                setCursor(e.target.selectionStart);
                const txt = transform(e.target.value, e.target.selectionStart, e.target.selectionEnd, (x) => {
                    setCursor(x);
                });
                onChange(txt || e.target.value);
                enableHelp(txt?.slice(0, e.target.selectionStart || 0).endsWith(';') || false);
            }} onKeyPress={(e) => {
                if (e.code === 'Enter' || e.code === 'NumpadEnter') {
                    oe();
                }
            }} />
    );
};
