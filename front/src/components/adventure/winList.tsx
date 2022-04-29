import { Collection, Level } from "./Adventure";

const storageKey = "winlist";

const loadWinList = (): string[] => {
    return JSON.parse(localStorage.getItem(storageKey) || "[]");
};

export const addToWinList = (level: string) => {
    const winList = loadWinList();
    winList.push(level);
    localStorage.setItem(storageKey, JSON.stringify(winList));
};

export const isWin = (level: string) => {
    const winList = loadWinList();
    return winList.find((x) => x === level) !== undefined;
};

export const isWinNode = (node: Level | Collection): boolean => {
    if (node.type === 'level') {
        return isWin(node.id);
    }
    return node.children.find((x) => !isWinNode(x)) === undefined;
};
