import { Instance } from "../pkg/hakim_wasm";
import "./my.css";

const title = document.createElement('h1');
title.innerText = document.title = 'Hello Hakim';
document.body.appendChild(title);

const instance = new Instance()
instance.load_library('Arith');
instance.load_library('Logic');
instance.start_session("forall a b: U, forall f: forall x: a, b, forall x y: a, forall p: eq a x y, eq b (f x) (f y)");

window.instance = instance;

const monitor = document.createElement('div');
document.body.appendChild(monitor);

const inp = document.createElement('input');
inp.type = 'text';
document.body.appendChild(inp);

document.body.appendChild(document.createElement('p'));

const newGoal = document.createElement('button');
newGoal.innerText = 'New Goal';
document.body.appendChild(newGoal);

const setGoal = (x) => {
    const error = instance.start_session(x);
    if (error) {
        alert(error);
        return;
    }
    update();
}

newGoal.onclick = () => setGoal(window.prompt('New Goal?'));

const undo = document.createElement('button');
undo.innerText = 'Undo';
document.body.appendChild(undo);
undo.onclick = () => {
    tacticAndUpdate('Undo');
};

window.ask_question = (x) => {
    return window.prompt(x);
};
window.panic_handler = (x) => {
    document.body.innerHTML = `<pre>${x}</pre>`;
};

const auto_goal = document.createElement('button');
auto_goal.innerText = 'Automatic proof is available';
auto_goal.style.display = 'none';
document.body.appendChild(auto_goal);


const history = document.createElement('ul');
document.body.appendChild(history);

const update = () => {
    monitor.innerHTML = '';
    auto_goal.style.display = 'none';
    while (history.lastChild) {
        history.removeChild(history.lastChild);
    }
    const hl = instance.get_history();
    for (const h of hl) {
        const li = document.createElement('li');
        li.innerText = h;
        history.appendChild(li);
    }
    let m = instance.monitor();
    if (m == 'Finished') {
        monitor.innerText = 'Proof is complete.';
        return;
    }
    const { goals, hyps } = m.Monitor;
    for (const hyp of hyps) {
        const d = document.createElement('div');
        d.className = 'backgreen';
        d.innerText = `${hyp[0]}: ${hyp[1]}`;
        d.addEventListener('dblclick', () => {
            suggestion_on_hyp_dblclk(hyp[0]);
        });
        monitor.appendChild(d);
    }
    let i = 0;
    for (const goal of goals) {
        monitor.appendChild(document.createElement('hr'));
        const d = document.createElement('div');
        if (i == 0) {
            d.className = 'backgreen';
            d.addEventListener('dblclick', () => {
                suggestion_on_goal_dblclk();
            });
        }
        d.innerText = goal;
        monitor.appendChild(d);
        i += 1;
    }
    const auto_tactic = instance.try_auto();
    if (auto_tactic) {
        auto_goal.style.display = 'inline';
        auto_goal.onclick = () => {
            tacticAndUpdate(auto_tactic);
        }
    }
};
update();

const tacticAndUpdate = (x) => {
    const error = instance.run_tactic(x);
    if (error) {
        alert(error);
        return false;
    }
    update();
    return true;
};

const suggestion_on_goal_dblclk = () => {
    const error = instance.suggest_dblclk_goal();
    if (error) {
        alert(error);
        return false;
    }
    update();
    return true;
};

const suggestion_on_hyp_dblclk = (name) => {
    const error = instance.suggest_dblclk_hyp(name);
    if (error) {
        alert(error);
        return false;
    }
    update();
    return true;
};

inp.addEventListener('keydown', (e) => {
    if (e.code === 'Enter') {
        if (tacticAndUpdate(inp.value)) {
            inp.value = '';
        }
    }
});

const exampleGoals = [
    '∀ a b c d: ℤ, a < b -> c < d -> a + c < b + d',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, P x',
    '∀ a: ℤ, ∃ b: ℤ, a < b',
    '∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False',
];

const exampleSection = document.createElement('div');
for (const ex of exampleGoals) {
    const b = document.createElement('button');
    b.innerText = ex;
    b.onclick = () => {
        setGoal(ex);
    };
    exampleSection.appendChild(b);
}

document.body.appendChild(exampleSection);

const sr_title = document.createElement('h1');
sr_title.innerText = 'Search';
document.body.appendChild(sr_title);
const sr = document.createElement('input');
sr.type = 'text';
document.body.appendChild(sr);
const sr_val = document.createElement('pre');
sr_val.innerText = 'Type search query and press enter';
document.body.appendChild(sr_val);

sr.addEventListener('keydown', (e) => {
    if (e.code === 'Enter') {
        const r = instance.search(sr.value);
        sr_val.innerText = r;
    }
});

const help = document.createElement('div');

help.innerHTML = `
<h1>Help</h1>
<p>tactics available:</p>
<ul>
    <li>intros</li>
    <li>rewrite</li>    
    <li>apply</li>
    <li>ring</li>
</ul>
`;

document.body.appendChild(help);
