#!/bin/bash
shopt -s expand_aliases
source ~/.bashrc
Start=`date +%F | sed 's/-//g'``date +%T | sed 's/://g'`
dafny n_mutualEx_lemma_oninv__1.dfy
dafny n_mutualEx_lemma_oninv__2.dfy
dafny n_mutualEx_lemma_oninv__3.dfy
dafny n_mutualEx_lemma_oninv__4.dfy
dafny n_mutualEx_lemma_oninv__5.dfy
End=`date +%F | sed 's/-//g'``date +%T | sed 's/://g'`
val=`expr $End - $Start`
printf "%s %.2f sec\n" 运行时间为： $val

