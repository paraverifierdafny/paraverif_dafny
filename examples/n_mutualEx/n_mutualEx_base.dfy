//(*  Title:      HOL/Auth/n_mutualEx_base.dfy
 //   Author:    Jiang Hongjian, ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
 //   Copyright    2020 ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
//*)

//header{*The n_mutualEx Protocol Case Study*} 

//theory n_mutualEx_base imports paraTheory
//begin

//section{*Main definitions of dafny  file*}

//subsection{* Definitions of Constants*}

datatype state = I| T| C| E
type client=nat
type boolean=bool

