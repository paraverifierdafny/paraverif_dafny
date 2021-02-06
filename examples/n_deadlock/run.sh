#!/bin/bash
shopt -s expand_aliases
source ~/.bashrc
dafny n_deadlock_lemma_oninv__1.dfy
dafny n_deadlock_lemma_oninv__2.dfy
dafny n_deadlock_lemma_oninv__3.dfy
dafny n_deadlock_lemma_oninv__4.dfy
dafny n_deadlock_lemma_oninv__5.dfy
