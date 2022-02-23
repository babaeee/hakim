import enDict from "./en.yml";
import faDict from "./fa.yml";

let dict: any = {};

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

export const getText = (id: string): string => {
  return dict[id] || id;
};

export const g = (c: TemplateStringsArray, ...v: string[]) => {
  const t = c.map((x) => x.split(' ').map(getText).join(' '));
  v.push('');
  const r = t.map((x, i) => `${x}\u2068${v[i]}\u2069`).join('');
  return r;
};

export const fromRust = (s: string) => {
  return s.replace(/\$\w+/g, (x) => getText(x.slice(1)));
};

init();
