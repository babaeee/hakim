import { Fragment, useContext } from "react";
import { useDrag } from "react-dnd";
import { sendTactic } from "../../../hakim";
import { ProofContext } from "../Proof";
import css from "./Sidebar.module.css";

const Lemma = ({ name, ty }: { name: string, ty: string }) => {
    const [, drag] = useDrag(() => ({
        type: 'Hyp',
        item: () => ({ name }),
    }), [name]);
    return (
        <div ref={drag}
            onDoubleClick={async () => {
                await sendTactic(`add_from_lib ${name}`);
            }}
            dir="ltr" className={css.lemma} title={ty}>{name}</div>
    );
};

export const LemmaBox = () => {
    const { lemmaBox } = useContext(ProofContext);
    return (
        <div className={css.base}>
            <div className={css.lemmaBox}>
                {lemmaBox.map(({ name, ty }) => <Fragment key={name}><Lemma name={name} ty={ty} /> </Fragment>)}
            </div>
        </div>
    );
};
