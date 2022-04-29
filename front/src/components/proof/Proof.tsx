import css from './Proof.module.css';
import { g } from '../../i18n';
import { History } from './sidebar/History';
import { Toolbar } from './Toolbar';
import { Tabs } from './tabs/Tabs';
import { LemmaBox } from './sidebar/LemmaBox';
import { createContext, useState } from 'react';
import { DndProvider } from 'react-dnd'
import { HTML5Backend } from 'react-dnd-html5-backend'
import { cancelProof, solveProof } from '../root/Root';
import { useNavigate } from 'react-router-dom';

type Lemma = {
  name: string,
  ty: string,
};

type ProofContextType = {
  onFinish: (won: boolean) => void,
  lemmaBox: Lemma[],
  appendLemma: (lemma: Lemma) => void,
};

export const ProofContext = createContext({} as ProofContextType);

export const Proof = () => {
  const [lemmaBox, setLemmaBox] = useState([] as Lemma[]);
  const navigator = useNavigate();
  const [natural, setNatural] = useState(undefined as string | undefined);
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
          <button className={css.changeLangButton} onClick={() => onFinish(false)}>{g`exit`}</button>
        </h1>
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
