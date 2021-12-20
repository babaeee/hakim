import { useState } from "react";
import { UnicodeHelp } from "../components/unicode/UnicodeHelp";
import { UnicodeInput } from "../components/unicode/UnicodeInput";
import { isRTL } from "../i18n";
import css from "./dialog.module.css";

type Props = {
  msg: string,
  onDone: (r: string) => any,
};

export const NormalPrompt = ({ msg, onDone }: Props) => {
  const [value, setValue] = useState('');
  const [help, setHelp] = useState(false);
  return (
    <div>
      <div className={css.background} onClick={() => onDone(value)} />
      <div className={css.foreground}>
        <p dir={isRTL() ? 'rtl' : 'ltr'}>{msg}</p>
        <UnicodeInput className={css.input} value={value} onEnter={() => onDone(value)} onChange={setValue} enableHelp={setHelp} />
        <div>
          {help && <UnicodeHelp />}
        </div>
      </div>
    </div>
  )
};
