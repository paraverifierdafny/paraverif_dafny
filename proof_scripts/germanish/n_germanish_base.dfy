//(*  Title:      HOL/Auth/n_germanish_base.dfy
 //   Author:    Jiang Hongjian, ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
 //   Copyright    2020 ShangHai Key Laboratory of Trustworthy Computing, East China Normal University
//*)

//header{*The n_germanish Protocol Case Study*} 

//theory n_germanish_base imports paraTheory
//begin

//section{*Main definitions of dafny  file*}

//subsection{* Definitions of Constants*}

datatype channelType = epsilon| req_shared| req_exclusive
datatype cacheType = invalid| shared| exclusive
type client=nat
type boolean=bool

