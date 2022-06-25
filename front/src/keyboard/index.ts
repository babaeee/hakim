type EventListener = {
    priority: number,
    f: (ev: KeyboardEvent) => any
};
let listeners: EventListener[] = [];

window.addEventListener('keydown', (e) => {
    if (listeners.length === 0) return;
    const maxPriority = listeners.reduce((acc, cur) => acc.priority > cur.priority ? acc : cur);
    maxPriority.f(e);
});

export const subscribeKeyboard = (priority: number, f: (ev: KeyboardEvent) => any) => {
    listeners.push({ priority, f });
    return () => {
        listeners = listeners.filter((x) => x.f !== f);
    };
};
