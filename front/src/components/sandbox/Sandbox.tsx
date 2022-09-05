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
    'Goal (∀ donya_zibast: U, ∀ aye: donya_zibast, donya_zibast).\
Proof.\
intros.',
    'Goal (False).\
Proof.\
add_from_lib True_proof.',
    'Goal (∀ harchizi: U, False -> harchizi).\
Proof.\
intros.',
    'Goal (∀ ali_shad_ast: U, ∀ mohamad_shad_ast: U, ∀ khabar1: ali_shad_ast, ∀ khabar2: mohamad_shad_ast, ali_shad_ast ∧ mohamad_shad_ast).\
Proof.\
intros.',
    'Goal (∀ ali_shad_ast: U, ∀ mohamad_shad_ast: U, ∀ khabar1: ali_shad_ast,  ali_shad_ast ∨ mohamad_shad_ast).\
Proof.\
intros.',
    'Goal (∀ x y: Universe, x -> (x -> y) -> y).\
Proof.\
intros barf_ziad_mibarad madares_tatil_mishavad esbati_baraye_barfe_ziad esbati_baraye_agar_barf_ziad_biad_madrese_tatile.',
    'Goal (∀ gob:U,∀ khabar_bad_gob: gob -> False, ∀ khabar1: gob , False).\
Proof.\
intros hava_tarik_ast.\
intros khabar1.\
intros khabar2.',
    'Goal (∀ A B: U, ~ A ∨ B -> (A -> B)).\
Proof.\
intros barf_ziad_mibarad madares_tatil_mishavad .\
intros H.',
    'Goal (∀ A B : U, ~ (A ∨ B) -> ~A ∧ ~ B).\
Proof.\
intros ali_shad_ast mohamad_shad_ast.\
intros H.',
    'Goal (∀ x: ℤ, x = 2 -> x ^ 2 = 4).\
Proof.',
    'Goal ((∀ T: set ℤ, (∀ x:ℤ, ~ x ∈ T) -> T = {}) -> ∀ A: set ℤ , A ∩ {} = {}).\
Proof.\
intros farz.',
    'Goal (∀ A B: set ℤ, (A ∖ B) ∪ (A ∩ B) = A).\
Proof.\cd \
intros.',
    'finite { x: ℤ | prime x} -> False',
    '∀ A: U, ∀ a: A, a ∈ {} -> False',
    '∀ T: U, ∀ a: T, ∀ S: set T, a ∈ S -> { a } ∪ (S ∖ { a }) = S',
    '∀ a b c d: ℤ, a < b -> c < d -> a + c < b + d',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, P x',
    '∀ a: ℤ, ∃ b: ℤ, a < b',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False',
    '∀ n: ℤ, 0 ≤ n → 2 * (Σ i in [0, n + 1) i) = n * (n + 1)',
    '∀ n: ℤ, 0 ≤ n → (Σ i in [0, n) 2 ^ i) = 2 ^ n - 1',
    '∀ n: ℤ, 0 ≤ n → (Σ i in [0, n) 2 * i + 1) = n * n',
    '∀ n: ℤ, 0 ≤ n → (Σ i in [- n, n + 1) |i|) = 2 * Σ i in [0, n + 1) |i|',
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
            <div>
                <span className={css.text}>{g`engine_params`}:</span>
                <UnicodeInput
                    style={{ width: '80%' }}
                    value={engineParams} onChange={setEngineParams} enableHelp={setHelp} />
            </div>
            {help && <div className={css.unicodeHelp} dir="ltr"><UnicodeHelp /></div>}
            <p className={css.text}>{g`or_choose_one_prop`}</p>
            <ul dir="ltr" className={css.exampleSection}>
                {exampleGoals.map((g) => <><li key={g} onClick={() => done(g)} className={css.exampleItem}>{g}</li>{' '}</>)}
            </ul>
            <button onClick={() => window.history.back()}>{g`back`}</button>
        </div>
    );
};
