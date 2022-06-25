import { useEffect, useState } from "react";
import { UnicodeHelp } from "../components/unicode/UnicodeHelp";
import { UnicodeInput } from "../components/unicode/UnicodeInput";
import { isRTL } from "../i18n";
import { subscribeKeyboard } from "../keyboard";
import css from "./dialog.module.css";

type Props = {
  msg: string,
  onDone: (r: string) => any,
  defaultValue: string,
};

export const NormalPrompt = ({ msg, onDone, defaultValue }: Props) => {
  const [value, setValue] = useState(defaultValue);
  const [help, setHelp] = useState(false);
  const [killed, setKilled] = useState(false);
  const myDone = (x: string) => {
    onDone(x);
    setKilled(true);
  };
  useEffect(() => {
    if (killed) return;
    return subscribeKeyboard(1000, () => { });
  }, [killed]);
  if (killed) return <></>;
  return (
    <div>
      <div className={css.background} onClick={() => myDone(value)} />
      <div className={css.foreground}>
        <p className={css.myP} dir={isRTL() ? 'rtl' : 'ltr'}>{msg}</p>
        <UnicodeInput autoFocus className={css.input} value={value} onEnter={() => myDone(value)} onChange={setValue} enableHelp={setHelp} />
        <div>
          {help && <UnicodeHelp />}
        </div>
      </div>
    </div>
  )
};
