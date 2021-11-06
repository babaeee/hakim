import React from 'react';
import logo from './logo.svg';
import css from './App.module.css';

const App = () => {
  return (
    <div className={css.main}>
      <h1 className={css.title}>
        <span>babaee_coq</span>
        <button className={css.changeLangButton}>chang</button>
      </h1>
    </div>
  );
}

export default App;
