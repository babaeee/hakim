import All from "../../../library/All.v";
import Arith from "../../../library/Arith.v";
import Eq from "../../../library/Eq.v";
import Induction from "../../../library/Induction.v";
import Logic from "../../../library/Logic.v";
import NumberTheory from "../../../library/NumberTheory.v";
import ProductOperator from "../../../library/ProductOperator.v";
import Set from "../../../library/All.v";
import Sigma from "../../../library/Sigma.v";

export const loadLibText = () => {
    return {
        'All': All,
        'Arith': Arith,
        'Eq': Eq,
        'Induction': Induction,
        'Logic': Logic,
        'NumberTheory': NumberTheory,
        'ProductOperator': ProductOperator,
        'Set': Set,
        'Sigma': Sigma,
    };
};
