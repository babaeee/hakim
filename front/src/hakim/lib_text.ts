import Arith from "../../../library/Arith.v";
import Eq from "../../../library/Eq.v";
import Function from "../../../library/Function.v";
import Induction from "../../../library/Induction.v";
import Logic from "../../../library/Logic.v";
import NumberTheory from "../../../library/NumberTheory.v";
import ProductOperator from "../../../library/ProductOperator.v";
import Set from "../../../library/Set.v";
import Sigma from "../../../library/Sigma.v";

export const loadLibText = () => {
    return {
        '/Arith': Arith,
        '/Eq': Eq,
        '/Function': Function,
        '/Induction': Induction,
        '/Logic': Logic,
        '/NumberTheory': NumberTheory,
        '/ProductOperator': ProductOperator,
        '/Set': Set,
        '/Sigma': Sigma,
    };
};
