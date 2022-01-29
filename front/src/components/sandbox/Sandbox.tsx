import { useState } from "react";
import { g } from "../../i18n";
import css from "./Sandbox.module.css";

type SanboxProps = {
    onFinish: (goal: string) => void,
};
//∀ A: U, ∀ a: A, In A (empty A) a -> False
const exampleGoals = [
    '∀ A: U, ∀ a: A, a ∈ {} -> False',
    '∀ T: U, ∀ a: T, ∀ S: set T, a ∈ S -> { a } ∪ (S ∖ { a }) = S',
    '∀ a b c d: ℤ, a < b -> c < d -> a + c < b + d',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, P x',
    '∀ a: ℤ, ∃ b: ℤ, a < b',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False',
    '∀ n: ℤ, 2 * sigma 0 (n+1) (λ i: ℤ, i) = n * (n + 1)',
    '∀ A B: U, ∀ f: A -> B, ∀ x y: A, x = y -> f x = f y',
    '∀ T: U, ∀ A B C: set T, A ⊆ B -> B ⊆ C -> A ⊆ C',
];

export const Sandbox = ({ onFinish }: SanboxProps) => {
    const [text, setText] = useState("");
    return (
        <div className={css.main}>
            <h1 className={css.title}>{g`sandbox_title`}</h1>
            <p className={css.text}>{g`type_a_goal_to_proof`}</p>
            <input dir="ltr" type="text" onChange={(ev) => setText(ev.target.value)} value={text} />
            <button onClick={() => onFinish(text)}>{g`submit`}</button>
            <p className={css.text}>{g`or_choose_one_prop`}</p>
            <ul dir="ltr" className={css.exampleSection}>
                {exampleGoals.map((g) => <><li key={g} onClick={() => onFinish(g)} className={css.exampleItem}>{g}</li>{' '}</>)}
            </ul>
        </div>
    );
};
