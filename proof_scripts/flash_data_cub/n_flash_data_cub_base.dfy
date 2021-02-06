//(*  Title:      HOL/Auth/n_flash_data_cub_base.dfy
 //   Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
 //   Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
//*)

//header{*The n_flash_data_cub Protocol Case Study*} 

//theory n_flash_data_cub_base imports paraTheory
//begin

//section{*Main definitions of dafny  file*}

//subsection{* Definitions of Constants*}

datatype CACHE_STATE = CACHE_I| CACHE_S| CACHE_E
datatype NODE_CMD = NODE_None| NODE_Get| NODE_GetX
datatype UNI_CMD = UNI_None| UNI_Get| UNI_GetX| UNI_Put| UNI_PutX| UNI_Nak
datatype INV_CMD = INV_None| INV_Inv| INV_InvAck
datatype RP_CMD = RP_None| RP_Replace
datatype WB_CMD = WB_None| WB_Wb
datatype SHWB_CMD = SHWB_None| SHWB_ShWb| SHWB_FAck
datatype NAKC_CMD = NAKC_None| NAKC_Nakc
type NODE=nat
type DATA=nat
type boolean=bool

