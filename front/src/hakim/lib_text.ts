import Arith from "../../../library/Arith.v";
import RArith from "../../../library/RArith.v";
import Combinatorics from "../../../library/Combinatorics.v";
import Eq from "../../../library/Eq.v";
import Function from "../../../library/Function.v";
import Induction from "../../../library/Induction.v";
import Logic from "../../../library/Logic.v";
import NumberTheory from "../../../library/NumberTheory.v";
import ProductOperator from "../../../library/ProductOperator.v";
import Set from "../../../library/Set.v";
import Sigma from "../../../library/Sigma.v";
import List from "../../../library/List.v";
import Graph from "../../../library/Graph.v";
import Game from "../../../library/Game.v";
import Tuples from "../../../library/Tuples.v";
import EnumerativeCombinatorics from "../../../library/EnumerativeCombinatorics.v";

export const loadLibText = () => {
  return {
    "/Arith": Arith,
    "/RArith": RArith,
    "/Combinatorics": Combinatorics,
    "/Eq": Eq,
    "/Function": Function,
    "/Induction": Induction,
    "/Logic": Logic,
    "/NumberTheory": NumberTheory,
    "/ProductOperator": ProductOperator,
    "/Set": Set,
    "/Sigma": Sigma,
    "/List": List,
    "/Graph": Graph,
    "/Game": Game,
    "/Tuples": Tuples,
    "/EnumerativeCombinatorics": EnumerativeCombinatorics,
  };
};
