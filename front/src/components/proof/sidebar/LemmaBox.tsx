import { Fragment, useContext } from "react";
import { useDrag } from "react-dnd";
import { ProofContext } from "../Proof";
import css from "./Sidebar.module.css";

const Lemma = ({ name }: { name: string }) => {
    const [, drag] = useDrag(() => ({
        type: 'Hyp',
        item: () => ({ name }),
    }), [name]);
    return (
        <div ref={drag} className={css.lemma}>{name}</div>
    );
};

export const LemmaBox = () => {
    const { lemmaBox } = useContext(ProofContext);
    return (
        <div className={css.base}>
            <div className={css.lemmaBox}>
                {lemmaBox.map((x) => <Fragment key={x}><Lemma name={x} /> </Fragment>)}
            </div>
        </div>
    );
};
