import enDict from "./en.yml";
import faDict from "./fa.yml";

let dict: { [s: string]: string } = {};

export const getLang = () => {
  return localStorage.getItem('lang') || 'fa';
};

export const changeLang = () => {
  console.log('lang changed');
  const to = getLang() === 'fa' ? 'en' : 'fa';
  localStorage.setItem('lang', to);
  window.location.reload();
};

export const isRTL = () => {
  return getLang() === 'fa';
};

export const init = () => {
  const lang = getLang();
  if (lang === 'fa') dict = faDict;
  if (lang === 'en') dict = enDict;
};

export const getText = (inp: string): string => {
  const [id, argsText] = inp.split('<$');
  let r = dict[id] || id;
  if (!argsText) {
    return r;
  }
  const args = argsText.slice(0, -2).split('$,');
  let i = 0;
  for (const arg of args) {
    r = r.replaceAll(`$${i}`, arg);
    i += 1;
  }
  return r;
};

export const g = (c: TemplateStringsArray, ...v: string[]) => {
  const t = c.map((x) => x.split(' ').map(getText).join(' '));
  v.push('');
  const r = t.map((x, i) => `${x}\u2068${v[i]}\u2069`).join('');
  return r;
};

export const fromRust = (s: string) => {
  return s.replace(/\$\w+(<\$.*\$>)?/g, (x) => getText(x.slice(1)));
};

init();
