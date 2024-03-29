import css from './Proof.module.css';
import { g } from '../../i18n';
import { History } from './sidebar/History';
import { Toolbar } from './Toolbar';
import { Tabs } from './tabs/Tabs';
import { LemmaBox } from './sidebar/LemmaBox';
import { createContext, useState } from 'react';
import { DndProvider } from 'react-dnd'
import { HTML5Backend } from 'react-dnd-html5-backend'
import { cancelProof, proofState, solveProof, Lemma } from '../root/Root';
import { useNavigate } from 'react-router-dom';
import { Title } from '../util/Title';
import Markdown from "markdown-it";

const markdown = new Markdown();

type MouseTarget = { kind: "goal" } | { kind: "hyp" | "lem", name: string }

type ActionHint = {
  kind: "dblClick",
  target: MouseTarget,
} | {
  kind: "newAssert",
}

type ProofContextType = {
  onFinish: (won: boolean) => void,
  lemmaBox: Lemma[],
  appendLemma: (lemma: Lemma) => void,
  actionHint: ActionHint | undefined,
  setActionHint: (actionHint: ActionHint | undefined) => any,
};

const HeadText: React.FC<{ text: string | undefined }> = ({ text }) => {
  const [hide, setHide] = useState(false);
  if (!text || text === '') {
    return <></>;
  }
  if (hide) {
    const t = text.trim().split(/(\s+)/).slice(0, 20).join(' ');
    return <p className={css.text}>{t} ... <button onClick={() => setHide(!hide)}>{g`show_it`}</button></p>
  }
  return <><div className={css.text}><p dangerouslySetInnerHTML={{
    __html: markdown.render(text),
  }} /> <button onClick={() => setHide(!hide)}>{g`hide_it`}</button></div></>;
}

export const ProofContext = createContext({} as ProofContextType);

export const Proof = () => {
  const [lemmaBox, setLemmaBox] = useState(proofState.suggestedLemmas);
  const navigator = useNavigate();
  const [natural, setNatural] = useState(undefined as string | undefined);
  const [actionHint, setActionHint] = useState(undefined as any);
  if (natural) {
    return <div className={css.inlBody}>
      <pre>
        {natural}
      </pre>
      <button onClick={() => setNatural(undefined)}>{g`back`}</button>
    </div>;
  }
  const onFinish = (won: boolean) => {
    if (won) {
      solveProof(navigator);
    } else {
      cancelProof(navigator);
    }
  };

  const ctx: ProofContextType = {
    lemmaBox,
    actionHint,
    setActionHint,
    appendLemma: (lemma) => {
      if (lemmaBox.find((x) => x.name === lemma.name)) {
        return;
      }
      setLemmaBox([...lemmaBox, lemma]);
    },
    onFinish,
  };
  return (
    <DndProvider backend={HTML5Backend}><ProofContext.Provider value={ctx}>
      <Title title={g`proof_screen`} />
      <div className={css.main}>
        <HeadText text={proofState.text} />
        <div className={css.bottomContainer}>
          <Toolbar />
          <Tabs />
          <div className={css.sidebarContainer}>
            <History onNatural={setNatural} />
            <LemmaBox />
          </div>
        </div>
      </div>
    </ProofContext.Provider></DndProvider>
  );
};
