import { Instance } from "../pkg/hakim_wasm";

const title = document.createElement('h1');
title.innerText = document.title = 'Hello Hakim';
document.body.appendChild(title);

const instance = new Instance("forall a b: U, forall f: forall x: a, b, forall x y: a, forall p: eq a x y, eq b (f x) (f y)");

const monitor = document.createElement('pre');
monitor.innerText = instance.monitor();
document.body.appendChild(monitor);

const inp = document.createElement('input');
inp.type = 'text';
document.body.appendChild(inp);
inp.addEventListener('keydown', (e) => {
    if (e.code === 'Enter') {
        const error = instance.run_tactic(inp.value);
        if (error) {
            alert(error);
            return;
        }
        monitor.innerText = instance.monitor();
        inp.value = '';
    }
});
