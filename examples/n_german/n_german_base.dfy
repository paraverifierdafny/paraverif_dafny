//(*  Title:      HOL/Auth/n_german_base.dfy
 //   Author:    Jiang Hongjian, ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
 //   Copyright    2020 ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
//*)

//header{*The n_german Protocol Case Study*} 

//theory n_german_base imports paraTheory
//begin

//section{*Main definitions of dafny  file*}

//subsection{* Definitions of Constants*}

datatype CACHE_STATE = I| S| E
datatype MSG_CMD = Empty| ReqS| ReqE| Inv| InvAck| GntS| GntE
type NODE=nat
type DATA=nat
type boolean=bool

