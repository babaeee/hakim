import { Instance } from "../pkg/hakim_wasm";

const title = document.createElement('h1');
title.innerText = document.title = 'Hello Hakim';
document.body.appendChild(title);

const instance = new Instance()
instance.load_library('Arith');
instance.load_library('Logic');
instance.start_session("forall a b: U, forall f: forall x: a, b, forall x y: a, forall p: eq a x y, eq b (f x) (f y)");

const monitor = document.createElement('pre');
monitor.innerText = instance.monitor();
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
}

const history = document.createElement('ul');
document.body.appendChild(history);

const update = () => {
    monitor.innerText = instance.monitor();
    while (history.lastChild) {
        history.removeChild(history.lastChild);
    }
    const hl = instance.get_history();
    for (const h of hl) {
        const li = document.createElement('li');
        li.innerText = h;
        history.appendChild(li);
    }
};

const tacticAndUpdate = (x) => {
    const error = instance.run_tactic(x);
    if (error) {
        alert(error);
        return false;
    }
    update();
    return true;
}

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
