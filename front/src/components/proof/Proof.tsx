import css from './Proof.module.css';
import { changeLang, g } from '../../i18n';
import { History } from './sidebar/History';
import { Toolbar } from './Toolbar';
import { Tabs } from './tabs/Tabs';
import { LemmaBox } from './sidebar/LemmaBox';
import { createContext, useState } from 'react';
import { DndProvider } from 'react-dnd'
import { HTML5Backend } from 'react-dnd-html5-backend'

type ProofProps = {
  onFinish: () => void;
};

type Lemma = {
  name: string,
  ty: string,
};

type ProofContextType = {
  onFinish: () => void,
  lemmaBox: Lemma[],
  appendLemma: (lemma: Lemma) => void,
};

export const ProofContext = createContext({} as ProofContextType);

export const Proof = ({ onFinish }: ProofProps) => {
  const [lemmaBox, setLemmaBox] = useState([] as Lemma[]);
  const ctx: ProofContextType = {
    lemmaBox,
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
      <div className={css.main}>
        <h1 className={css.title}>
          <span>{g`babaeee_coq`}</span>
          <button className={css.changeLangButton} onClick={changeLang}>{g`change_lang`}</button>
          <button className={css.changeLangButton} onClick={onFinish}>{g`exit`}</button>
        </h1>
        <div className={css.bottomContainer}>
          <Toolbar />
          <Tabs />
          <div className={css.sidebarContainer}>
            <History />
            <LemmaBox />
          </div>
        </div>
      </div>
    </ProofContext.Provider></DndProvider>
  );
};
