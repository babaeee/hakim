import enDict from "./en.yml";
import faDict from "./fa.yml";

let dict: any = {};

export const getLang = () => {
  return localStorage.getItem('lang') || 'en';
};

export const changeLang = () => {
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
  const r = t.map((x, i) => x + v[i]).join('');
  return r;
};

init();
