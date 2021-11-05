import "./menu.css";

let menu = undefined;

const removeMenu = () => {
    if (!menu || !menu.parentElement) return;
    console.log(menu);
    menu.parentElement.removeChild(menu);
    menu = undefined;
};

document.body.addEventListener('click', () => {
    removeMenu();
});

export const createMenu = (items, ele, ev) => {
    removeMenu();
    menu = document.createElement('ul');
    for (const item of items) {
        const li = document.createElement('li');
        li.innerText = item.label;
        li.onclick = () => {
            removeMenu();
            item.action();
        };
        menu.appendChild(li);
    }
    const rect = document.body.getBoundingClientRect();
    const x = ev.clientX - rect.left;
    const y = ev.clientY - rect.top;

    // Set the position for menu
    menu.className = 'menu';
    menu.style.top = `${y}px`;
    menu.style.left = `${x}px`;

    ele.appendChild(menu);
};
