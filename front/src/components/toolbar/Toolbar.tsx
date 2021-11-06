import { sendTactic } from "../../hakim";
import { g } from "../../i18n";
import css from "./toolbar.module.css";

export const ToolButton = ({ label, onClick }: { label: string, onClick: any }) => {
    return (
        <button className={css.toolButton} onClick={onClick}>
            {label}
        </button>
    );
}

const newAssert = () => {
    const inp = window.prompt(g`input_assertion`);
    sendTactic(`add_hyp (${inp})`);
};

export const Toolbar = () => {
    return (
        <div className={css.toolContain}>
            <ToolButton onClick={newAssert} label={g`new_assertion`} />
            <ToolButton onClick={() => { }} label="1" />
            <ToolButton onClick={() => { }} label="1" />
        </div>
    );
};