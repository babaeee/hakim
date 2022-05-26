import { useState } from "react";
import { useNavigate } from "react-router-dom";
import { sendTactic, setGoal } from "../../hakim";
import { g } from "../../i18n";
import { openProofSession } from "../root/Root";
import { UnicodeHelp } from "../unicode/UnicodeHelp";
import { UnicodeInput } from "../unicode/UnicodeInput";
import { Title } from "../util/Title";
import css from "./Sandbox.module.css";

//∀ A: U, ∀ a: A, In A (empty A) a -> False
const exampleGoals = [
    'finite ℤ { x: ℤ | prime x} -> False',
    '∀ A: U, ∀ a: A, a ∈ {} -> False',
    '∀ T: U, ∀ a: T, ∀ S: set T, a ∈ S -> { a } ∪ (S ∖ { a }) = S',
    '∀ a b c d: ℤ, a < b -> c < d -> a + c < b + d',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, P x',
    '∀ a: ℤ, ∃ b: ℤ, a < b',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False',
    '∀ n: ℤ, 0 ≤ n -> 2 * sigma 0 (n+1) (λ i: ℤ, i) = n * (n + 1)',
    '∀ n: ℤ, 0 ≤ n -> sigma 0 n (λ i: ℤ, 2 ^ i) = 2 ^ n - 1',
    '∀ n: ℤ, 0 ≤ n -> sigma (-n) (n+1) (λ i: ℤ, |i|) = 2 * sigma 0 (n+1) (λ i: ℤ, |i|)',
    '∀ A B: U, ∀ f: A -> B, ∀ x y: A, x = y -> f x = f y',
    '∀ T: U, ∀ A B C: set T, A ⊆ B -> B ⊆ C -> A ⊆ C',
    '∀ n: ℤ, 2 < n -> ∀ a b c, a ^ n + b ^ n = c ^ n -> False',
];

export const Sandbox = () => {
    const [text, setText] = useState("");
    const [engineParams, setEngineParams] = useState("");
    const [help, setHelp] = useState(false);
    const navigator = useNavigate();
    const done = async (t = text) => {
        const goal = t.trim();
        let toProof = false;
        if (goal.startsWith('Goal')) {
            const [g, , ...v] = goal.split('.');
            if (!await setGoal(g.slice(6, -1))) {
                return;
            }
            for (const xs of v) {
                const x = xs.trim();
                if (x === '') continue;
                if (!await sendTactic(x)) {
                    return;
                }
            }
            toProof = true;
        } else if (await setGoal(t, '/', engineParams)) {
            toProof = true;
        }
        if (toProof) {
            openProofSession(navigator);
        }
    };
    return (
        <div className={css.main}>
            <Title title={g`sandbox`} />
            <h1 className={css.title}>{g`sandbox`}</h1>
            <p className={css.text}>{g`type_a_goal_to_proof`}</p>
            <UnicodeInput value={text} onChange={setText} enableHelp={setHelp} onEnter={done} />
            <button onClick={() => done()}>{g`submit`}</button>
            <UnicodeInput value={engineParams} onChange={setEngineParams} enableHelp={setHelp} />
            {help && <div className={css.unicodeHelp} dir="ltr"><UnicodeHelp /></div>}
            <p className={css.text}>{g`or_choose_one_prop`}</p>
            <ul dir="ltr" className={css.exampleSection}>
                {exampleGoals.map((g) => <><li key={g} onClick={() => done(g)} className={css.exampleItem}>{g}</li>{' '}</>)}
            </ul>
            <button onClick={() => window.history.back()}>{g`back`}</button>
        </div>
    );
};
