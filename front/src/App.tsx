import React from 'react';
import logo from './logo.svg';
import css from './App.module.css';
import { changeLang, g, isRTL } from './i18n';
import { Monitor } from './components/monitor/Monitor';
import { History } from './components/history/history';
import { Toolbar } from './components/toolbar/Toolbar';

const App = () => {
  return (
    <div dir={isRTL() ? 'rtl' : 'ltr'} className={css.main}>
      <h1 className={css.title}>
        <span>{g`babaeee_coq`}</span>
        <button className={css.changeLangButton} onClick={changeLang}>{g`change_lang`}</button>
      </h1>
      <div className={css.bottomContainer}>
        <Toolbar />
        <Monitor />
        <div className={css.sidebarContainer}>
          <History />
          <History />
        </div>
      </div>
    </div>
  );
}

export default App;
