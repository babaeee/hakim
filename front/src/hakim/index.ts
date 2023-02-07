import { normalPrompt } from "../dialog";
import { fromRust } from "../i18n";
import { loadLibText } from "./lib_text";
import { hakimQueryImpl } from "./network_provider";

declare let window: Window & {
  ask_question: (q: string) => Promise<string>;
  panic_handler: (s: string) => void;
  load_lib_json: () => object;
  hakimQuery: (x: any) => any;
  hakimQueryLoad: Promise<void>;
  hardReset: () => void;
  instance: Instance;
};

window.ask_question = (x) => {
  return normalPrompt(fromRust(x));
};
window.panic_handler = (x) => {
  document.body.innerHTML = `<pre>${x}</pre>`;
};
window.load_lib_json = loadLibText;

const checkError = (error?: string) => {
  if (error) {
    alert(error);
    return false;
  }
  return true;
};

const wasmReset = () => {
  localStorage.removeItem("wasmState");
  window.onbeforeunload = null;
  window.location.reload();
};

window.hardReset = wasmReset;

const prevBackup = localStorage.getItem("wasmState");

type Instance = {
  [key: string]: (x?: any) => Promise<any>;
};

// await window.hakimQueryLoad;
// window.hakimQuery({ command: "load_lib", arg: window.load_lib_json() });

const instance: Instance = new Proxy(
  {},
  {
    get(_, prop) {
      return async (arg: any) => {
        try {
          let r = await hakimQueryImpl({ command: prop, arg });
          while (r && typeof r === "object" && r.AskQuestion) {
            const answer = await window.ask_question(r.AskQuestion);
            r = await hakimQueryImpl({
              command: "answer_question",
              arg: answer,
            });
          }
          return r;
        } catch (e) {
          console.log(e);
          document.body.innerHTML = "panic";
        }
      };
    },
  }
);

window.instance = instance;

if (prevBackup) {
  if (!instance.from_backup(JSON.parse(prevBackup))) {
    window.alert("backup version is incompatible. reloading...");
    wasmReset();
  }
}

export const toBackup = () => {
  return JSON.stringify(instance.to_backup());
};

export type State = {
  undoHistory: string[];
  redoHistory: string[];
} & (
  | { isFinished: true }
  | {
      isFinished: false;
      monitor: {
        hyps: string[];
        goals: string[];
      };
    }
);

type EventListener = (s: State) => void;

let listeners: EventListener[] = [];

const isState = (x: State): x is State => {
  if (!(x.undoHistory instanceof Array) || !(x.redoHistory instanceof Array)) {
    console.log("state does not have history\nState: " + JSON.stringify(x));
    return false;
  }
  if (x.isFinished === true) return true;
  if (x.isFinished !== false) return false;
  if (!x.monitor) return false;
  if (!(x.monitor.goals instanceof Array)) return false;
  if (!(x.monitor.hyps instanceof Array)) return false;
  return true;
};

const calcState = async (): Promise<State> => {
  const f = async (): Promise<State> => {
    const [undoHistory, redoHistory] = (await instance.get_history()) || [
      [],
      [],
    ];
    console.log(instance.monitor());
    const monitor = await instance.monitor();
    if (monitor === "Finished") {
      return { undoHistory, redoHistory, isFinished: true };
    }
    return {
      undoHistory,
      redoHistory,
      monitor: monitor.Running,
      isFinished: false,
    };
  };
  const r = await f();
  if (!isState(r)) {
    if (localStorage.getItem("wasmState") === null) {
      throw new Error("invalid state");
    }
    window.onbeforeunload = null;
    localStorage.removeItem("wasmState");
    localStorage.removeItem("reactState");
    window.location.reload();
  }
  return r;
};

export const emit = async () => {
  const v = await calcState();
  console.log("Emitted ", v, " to ", listeners.length, " people");
  listeners.forEach((f) => f(v));
};

export const subscribe = (f: EventListener) => {
  listeners.push(f);
  emit();
  return () => {
    listeners = listeners.filter((x) => x !== f);
  };
};

const checkErrorAndUpdate = async (
  error: () => Promise<string | undefined>
) => {
  if (checkError(await error())) {
    emit();
    return true;
  }
  return false;
};

export const getActionHint = (tactic: string) => {
  return instance.action_of_tactic(tactic);
};

export const sendTactic = (tactic: string) => {
  console.log(`tactic: `, tactic);
  return checkErrorAndUpdate(() => instance.run_tactic(tactic));
};

export const notationList = (): Promise<string[]> => {
  return instance.notation_list();
};

export const getNatural = async (): Promise<string> => {
  return fromRust((await instance.natural()) || "$invalid_state");
};

export const tryTactic = (tactic: string): boolean => {
  return true; //window.hakimQuery({ command: "try_tactic", arg: tactic });
};

export const check = (query: string): Promise<string> => {
  return instance.check(query);
};

export type SearchResult = {
  name: string;
  ty: string;
};

export const searchPattern = async (
  expr: string
): Promise<SearchResult[] | string> => {
  const r = await instance.search(expr);
  if (typeof r === "string") {
    return r;
  }
  return r.map(([a, b]: [string, string]) => {
    return {
      name: a,
      ty: b,
    };
  });
};

export const setGoal = (
  goal: string,
  libs: string = "/",
  params: string = ""
) => {
  localStorage.setItem("last_goal", `Goal (${goal})`);
  return checkErrorAndUpdate(() =>
    Promise.resolve(instance.start_session({ goal, libs, params }))
  );
};

export const runSuggMenuHyp = (hyp_name: string, index: number) => {
  return checkErrorAndUpdate(() =>
    instance.run_suggest_menu_hyp({ hyp_name, index })
  );
};

export const runSuggMenuGoal = (i: number) => {
  return checkErrorAndUpdate(() => instance.run_suggest_menu_goal(i));
};

export const runSuggDblGoal = () => {
  return checkErrorAndUpdate(() => instance.suggest_dblclk_goal());
};

export const runSuggDblHyp = (hyp: string) => {
  return checkErrorAndUpdate(() => instance.suggest_dblclk_hyp(hyp));
};

export const spanPosOfHyp = async (
  hyp: string,
  l: number,
  r: number
): Promise<number | undefined> => {
  return instance.pos_of_span_hyp({ hyp, l, r });
};
export const spanPosOfGoal = (
  l: number,
  r: number
): Promise<number | undefined> => {
  return instance.pos_of_span_goal({ l, r });
};

const parenSplit = (txt: string): string[] => {
  const r = [];
  let cur = "";
  let depth = 0;
  for (const c of txt) {
    if (c === "(") {
      depth += 1;
      if (depth === 1) continue;
    }
    if (c === ")") {
      depth -= 1;
      if (depth === 0) {
        r.push(cur);
        cur = "";
      }
    }
    if (depth > 0) {
      cur += c;
    }
  }
  return r.map((x) => fromRust(x));
};

export const suggMenuHyp = async (hypName: string) => {
  const suggs = await instance.suggest_menu_hyp(hypName);
  if (!suggs) return [];
  return parenSplit(suggs).map((x, i) => ({
    label: x,
    action: () => runSuggMenuHyp(hypName, i),
  }));
};

export const suggMenuGoal = async () => {
  const suggs = await instance.suggest_menu_goal();
  if (!suggs) return [];
  return parenSplit(suggs).map((x, i) => ({
    label: x,
    action: () => runSuggMenuGoal(i),
  }));
};

export type TryAutoResult =
  | {
      available: false;
    }
  | {
      available: true;
      type: "normal" | "history";
      tactic: string[];
    };

export const tryAuto = async (): Promise<TryAutoResult> => {
  const tactic = await instance.try_auto();
  if (tactic) {
    return {
      available: true,
      type: "normal",
      tactic: [tactic],
    };
  }
  const history_tactics = await instance.try_auto_history();
  if (history_tactics) {
    return {
      available: true,
      type: "history",
      tactic: history_tactics,
    };
  }
  return { available: false };
};

export type LibraryItemKind = "Import" | "Axiom" | "Suggestion" | "Theorem";

export type LibraryData = {
  name: string;
  rules: {
    kind: LibraryItemKind;
    name: string;
    ty?: string;
  }[];
};

export const fromMiddleOfLib = (
  lib: string,
  name: string,
  kind: LibraryItemKind
) => {
  // FIXME: return checkErrorAndUpdate(() =>
  // FIXME:   Promise.resolve(
  // FIXME:     instance.start_session_from_lib(lib, name, kind === "Theorem")
  // FIXME:   )
  // FIXME: );
};

export const allLibraryData = async (): Promise<LibraryData[]> => {
  const x = await instance.all_library_data();
  const convertRule = (r: any) => {
    const kind = Object.keys(r)[0];
    return {
      kind,
      ...r[kind],
    };
  };
  return Object.keys(x).map((a) => ({ name: a, rules: x[a].map(convertRule) }));
};
