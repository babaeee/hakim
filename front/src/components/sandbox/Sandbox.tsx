import { useState } from "react";
import { g } from "../../i18n";
import { UnicodeHelp } from "../unicode/UnicodeHelp";
import { UnicodeInput } from "../unicode/UnicodeInput";
import css from "./Sandbox.module.css";

type SanboxProps = {
    onFinish: (goal: string | undefined) => void,
};
//∀ A: U, ∀ a: A, In A (empty A) a -> False
const exampleGoals = [
    'finite ℤ { x: ℤ | prime x} -> False',
    '∀ A: U, ∀ a: A, a ∈ {} -> False',
    '∀ T: U, ∀ a: T, ∀ S: set T, a ∈ S -> { a } ∪ (S ∖ { a }) = S',
    '∀ a b c d: ℤ, a < b -> c < d -> a + c < b + d',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, P x',
    '∀ a: ℤ, ∃ b: ℤ, a < b',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False',
    '∀ n: ℤ, 0 < n + 1 -> 2 * sigma 0 (n+1) (λ i: ℤ, i) = n * (n + 1)',
    '∀ A B: U, ∀ f: A -> B, ∀ x y: A, x = y -> f x = f y',
    '∀ T: U, ∀ A B C: set T, A ⊆ B -> B ⊆ C -> A ⊆ C',
];

export const Sandbox = ({ onFinish }: SanboxProps) => {
    const [text, setText] = useState("");
    const [help, setHelp] = useState(false);
    const done = () => onFinish(text);
    return (
        <div className={css.main}>
            <h1 className={css.title}>{g`sandbox_title`}</h1>
            <p className={css.text}>{g`type_a_goal_to_proof`}</p>
            <UnicodeInput value={text} onChange={setText} enableHelp={setHelp} onEnter={done} />
            <button onClick={done}>{g`submit`}</button>
            {help && <div className={css.unicodeHelp} dir="ltr"><UnicodeHelp /></div>}
            <p className={css.text}>{g`or_choose_one_prop`}</p>
            <ul dir="ltr" className={css.exampleSection}>
                {exampleGoals.map((g) => <><li key={g} onClick={() => onFinish(g)} className={css.exampleItem}>{g}</li>{' '}</>)}
            </ul>
            <button onClick={() => onFinish(undefined)}>{g`back`}</button>
        </div>
    );
};
