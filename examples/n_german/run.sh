#!/bin/bash
shopt -s expand_aliases
source ~/.bashrc
Start=`date +%F | sed 's/-//g'``date +%T | sed 's/://g'`
dafny n_german_lemma_oninv__1.dfy
dafny n_german_lemma_oninv__2.dfy
dafny n_german_lemma_oninv__3.dfy
dafny n_german_lemma_oninv__4.dfy
dafny n_german_lemma_oninv__5.dfy
dafny n_german_lemma_oninv__6.dfy
dafny n_german_lemma_oninv__7.dfy
dafny n_german_lemma_oninv__8.dfy
dafny n_german_lemma_oninv__9.dfy
dafny n_german_lemma_oninv__10.dfy
dafny n_german_lemma_oninv__11.dfy
dafny n_german_lemma_oninv__12.dfy
dafny n_german_lemma_oninv__13.dfy
dafny n_german_lemma_oninv__14.dfy
dafny n_german_lemma_oninv__15.dfy
dafny n_german_lemma_oninv__16.dfy
dafny n_german_lemma_oninv__17.dfy
dafny n_german_lemma_oninv__18.dfy
dafny n_german_lemma_oninv__19.dfy
dafny n_german_lemma_oninv__20.dfy
dafny n_german_lemma_oninv__21.dfy
dafny n_german_lemma_oninv__22.dfy
dafny n_german_lemma_oninv__23.dfy
dafny n_german_lemma_oninv__24.dfy
dafny n_german_lemma_oninv__25.dfy
dafny n_german_lemma_oninv__26.dfy
dafny n_german_lemma_oninv__27.dfy
dafny n_german_lemma_oninv__28.dfy
dafny n_german_lemma_oninv__29.dfy
dafny n_german_lemma_oninv__30.dfy
dafny n_german_lemma_oninv__31.dfy
dafny n_german_lemma_oninv__32.dfy
dafny n_german_lemma_oninv__33.dfy
dafny n_german_lemma_oninv__34.dfy
dafny n_german_lemma_oninv__35.dfy
dafny n_german_lemma_oninv__36.dfy
dafny n_german_lemma_oninv__37.dfy
dafny n_german_lemma_oninv__38.dfy
dafny n_german_lemma_oninv__39.dfy
dafny n_german_lemma_oninv__40.dfy
dafny n_german_lemma_oninv__41.dfy
dafny n_german_lemma_oninv__42.dfy
dafny n_german_lemma_oninv__43.dfy
dafny n_german_lemma_oninv__44.dfy
dafny n_german_lemma_oninv__45.dfy
dafny n_german_lemma_oninv__46.dfy
dafny n_german_lemma_oninv__47.dfy
dafny n_german_lemma_oninv__48.dfy
dafny n_german_lemma_oninv__49.dfy
dafny n_german_lemma_oninv__50.dfy
dafny n_german_lemma_oninv__51.dfy
dafny n_german_lemma_oninv__52.dfy
dafny n_german_lemma_oninv__53.dfy
dafny n_german_lemma_oninv__54.dfy
dafny n_german_lemma_oninv__55.dfy
dafny n_german_lemma_oninv__56.dfy
dafny n_german_lemma_oninv__57.dfy
dafny n_german_lemma_oninv__58.dfy
End=`date +%F | sed 's/-//g'``date +%T | sed 's/://g'`
val=`expr $End - $Start`
printf "%s %.2f sec\n" 运行时间为： $val

