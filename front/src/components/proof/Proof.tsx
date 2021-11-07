import css from './Proof.module.css';
import { changeLang, g, isRTL } from '../../i18n';
import { Monitor } from './Monitor';
import { History } from './history';
import { Toolbar } from './Toolbar';

type ProofProps = {
  onFinish: () => void;
};

export const Proof = ({ onFinish }: ProofProps) => {
  return (
    <div dir={isRTL() ? 'rtl' : 'ltr'} className={css.main}>
      <h1 className={css.title}>
        <span>{g`babaeee_coq`}</span>
        <button className={css.changeLangButton} onClick={changeLang}>{g`change_lang`}</button>
      </h1>
      <div className={css.bottomContainer}>
        <Toolbar />
        <Monitor onFinish={onFinish} />
        <div className={css.sidebarContainer}>
          <History />
          <History />
        </div>
      </div>
    </div>
  );
};
