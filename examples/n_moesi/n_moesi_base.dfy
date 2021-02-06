//(*  Title:      HOL/Auth/n_moesi_base.dfy
 //   Author:    Jiang Hongjian, ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
 //   Copyright    2020 ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
//*)

//header{*The n_moesi Protocol Case Study*} 

//theory n_moesi_base imports paraTheory
//begin

//section{*Main definitions of dafny  file*}

//subsection{* Definitions of Constants*}

datatype locationType = M| OSTATUS| E| S| I
type client=nat
type boolean=bool

