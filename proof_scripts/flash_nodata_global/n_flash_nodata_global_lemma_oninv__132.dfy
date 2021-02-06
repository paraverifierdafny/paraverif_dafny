datatype CACHE_STATE = CACHE_I| CACHE_S| CACHE_E
datatype NODE_CMD = NODE_None| NODE_Get| NODE_GetX
datatype UNI_CMD = UNI_None| UNI_Get| UNI_GetX| UNI_Put| UNI_PutX| UNI_Nak
datatype INV_CMD = INV_None| INV_Inv| INV_InvAck
datatype RP_CMD = RP_None| RP_Replace
datatype WB_CMD = WB_None| WB_Wb
datatype SHWB_CMD = SHWB_None| SHWB_ShWb| SHWB_FAck
datatype NAKC_CMD = NAKC_None| NAKC_Nakc
type NODE=nat
type boolean=bool

class  class_0  {
var 
Cmd : NAKC_CMD
}


class  class_1  {
var 
HomeProc : boolean,
Proc : NODE,
Cmd : SHWB_CMD
}


class  class_2  {
var 
HomeInvSet : boolean,
InvSet : array<boolean>,
HomeShrSet : boolean,
ShrSet : array<boolean>,
ShrVld : boolean,
HomeHeadPtr : boolean,
HeadPtr : NODE,
HeadVld : boolean,
Dirty : boolean,
Local : boolean,
Pending : boolean
}


class  class_3  {
var 
CacheState : CACHE_STATE,
InvMarked : boolean,
ProcCmd : NODE_CMD
}


class  class_4  {
var 
NakcMsg_Cmd:NAKC_CMD,
ShWbMsg_HomeProc:boolean,
ShWbMsg_Proc:NODE,
ShWbMsg_Cmd:SHWB_CMD,
WbMsg_HomeProc:boolean,
WbMsg_Proc:NODE,
WbMsg_Cmd:WB_CMD,
HomeRpMsg_Cmd:RP_CMD,
RpMsg_Cmd:array<RP_CMD>,
HomeInvMsg_Cmd:INV_CMD,
InvMsg_Cmd:array<INV_CMD>,
HomeUniMsg_HomeProc:boolean,
HomeUniMsg_Proc:NODE,
HomeUniMsg_Cmd:UNI_CMD,
UniMsg_HomeProc:array<boolean>,
UniMsg_Proc:array<NODE>,
UniMsg_Cmd:array<UNI_CMD>,
Dir_HomeInvSet:boolean,
Dir_InvSet:boolean,
Dir_HomeShrSet:boolean,
Dir_ShrSet:boolean,
Dir_ShrVld:boolean,
Dir_HomeHeadPtr:boolean,
Dir_HeadPtr:NODE,
Dir_HeadVld:boolean,
Dir_Dirty:boolean,
Dir_Local:boolean,
Dir_Pending:boolean,
HomeProc_CacheState:CACHE_STATE,
HomeProc_InvMarked:boolean,
HomeProc_ProcCmd:NODE_CMD,
Proc_CacheState:array<CACHE_STATE>,
Proc_InvMarked:array<boolean>,
Proc_ProcCmd:array<NODE_CMD>
}
Sta_NakcMsg:,
Sta_ShWbMsg:,
Sta_WbMsg:,
Sta_HomeRpMsg:,
Sta_RpMsg:,
Sta_HomeInvMsg:,
Sta_InvMsg:,
Sta_HomeUniMsg:,
Sta_UniMsg:,
Sta_Dir:,
Sta_HomeProc:,
Sta_Proc:

//end
method n_NI_Local_Get_Put__part__0inv__132_0(                 
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Dirty[0] := false;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_S;
    Sta_UniMsg_Cmd[src] := UNI_Put;}
else{
    if (Sta_Dir_HeadVld[0] == true) {
      Sta_Dir_ShrVld[0] := true;
      Sta_Dir_ShrSet[src] := true;
      forall p  |0<= p<N0 {
        if ((p == src) || (Sta_Dir_ShrSet[p] == true)) {
          Sta_Dir_InvSet[p] := true;}
else{
          Sta_Dir_InvSet[p] := false;
        }
      }
      Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];}
else{
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
    }
    Sta_UniMsg_Cmd[src] := UNI_Put;
  }
}

method n_NI_Local_Get_Put__part__0inv__132_1(                 
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Dirty[0] := false;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_S;
    Sta_UniMsg_Cmd[src] := UNI_Put;}
else{
    if (Sta_Dir_HeadVld[0] == true) {
      Sta_Dir_ShrVld[0] := true;
      Sta_Dir_ShrSet[src] := true;
      forall p  |0<= p<N0 {
        if ((p == src) || (Sta_Dir_ShrSet[p] == true)) {
          Sta_Dir_InvSet[p] := true;}
else{
          Sta_Dir_InvSet[p] := false;
        }
      }
      Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];}
else{
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
    }
    Sta_UniMsg_Cmd[src] := UNI_Put;
  }
}

method n_NI_Local_Get_Put__part__0inv__132_2(                 
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Dirty[0] := false;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_S;
    Sta_UniMsg_Cmd[src] := UNI_Put;}
else{
    if (Sta_Dir_HeadVld[0] == true) {
      Sta_Dir_ShrVld[0] := true;
      Sta_Dir_ShrSet[src] := true;
      forall p  |0<= p<N0 {
        if ((p == src) || (Sta_Dir_ShrSet[p] == true)) {
          Sta_Dir_InvSet[p] := true;}
else{
          Sta_Dir_InvSet[p] := false;
        }
      }
      Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];}
else{
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
    }
    Sta_UniMsg_Cmd[src] := UNI_Put;
  }
}


method n_NI_Local_Get_Put__part__1inv__132_0(                  
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Dirty[0] := false;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_S;
    Sta_UniMsg_Cmd[src] := UNI_Put;}
else{
    if (Sta_Dir_HeadVld[0] == true) {
      Sta_Dir_ShrVld[0] := true;
      Sta_Dir_ShrSet[src] := true;
      forall p  |0<= p<N0 {
        if ((p == src) || (Sta_Dir_ShrSet[p] == true)) {
          Sta_Dir_InvSet[p] := true;}
else{
          Sta_Dir_InvSet[p] := false;
        }
      }
      Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];}
else{
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
    }
    Sta_UniMsg_Cmd[src] := UNI_Put;
  }
}

method n_NI_Local_Get_Put__part__1inv__132_1(                  
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Dirty[0] := false;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_S;
    Sta_UniMsg_Cmd[src] := UNI_Put;}
else{
    if (Sta_Dir_HeadVld[0] == true) {
      Sta_Dir_ShrVld[0] := true;
      Sta_Dir_ShrSet[src] := true;
      forall p  |0<= p<N0 {
        if ((p == src) || (Sta_Dir_ShrSet[p] == true)) {
          Sta_Dir_InvSet[p] := true;}
else{
          Sta_Dir_InvSet[p] := false;
        }
      }
      Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];}
else{
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
    }
    Sta_UniMsg_Cmd[src] := UNI_Put;
  }
}

method n_NI_Local_Get_Put__part__1inv__132_2(                  
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Dirty[0] := false;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_S;
    Sta_UniMsg_Cmd[src] := UNI_Put;}
else{
    if (Sta_Dir_HeadVld[0] == true) {
      Sta_Dir_ShrVld[0] := true;
      Sta_Dir_ShrSet[src] := true;
      forall p  |0<= p<N0 {
        if ((p == src) || (Sta_Dir_ShrSet[p] == true)) {
          Sta_Dir_InvSet[p] := true;}
else{
          Sta_Dir_InvSet[p] := false;
        }
      }
      Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];}
else{
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
    }
    Sta_UniMsg_Cmd[src] := UNI_Put;
  }
}


method n_NI_Local_GetX_PutX__part__0inv__132_0(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_1(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_2(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_3(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_4(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_5(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_6(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_7(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_8(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_9(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_10(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_11(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_12(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_13(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_14(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_15(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_16(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_17(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_18(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_19(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_20(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_21(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_22(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_23(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_24(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_25(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_26(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_27(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_28(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_29(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_30(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_31(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_32(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_33(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_34(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_35(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_36(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_37(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_38(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_39(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_40(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_41(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_42(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_43(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_44(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_45(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_46(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_47(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_48(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_49(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_50(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_51(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_52(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_53(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_54(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_55(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_56(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_57(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_58(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_59(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_60(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_61(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_62(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_63(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_64(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_65(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_66(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_67(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_68(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_69(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_70(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_71(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_72(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_73(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_74(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_75(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_76(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_77(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_78(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_79(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_80(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_81(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_82(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_83(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_84(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_85(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_86(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_87(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_88(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_89(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_90(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_91(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_92(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_93(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_94(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_95(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_96(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_97(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_98(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_99(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_100(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_101(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__0inv__132_102(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_Dirty[0] == true))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}


method n_NI_Local_GetX_PutX__part__1inv__132_0(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_1(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_2(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_3(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_4(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_5(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_6(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_7(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_8(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_9(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_10(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_11(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_12(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_13(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_14(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_15(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_16(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_17(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_18(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_19(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_20(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_21(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_22(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_23(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_24(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_25(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_26(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_27(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_28(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_29(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_30(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_31(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_32(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_33(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_34(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_35(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_36(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_37(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_38(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_39(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_40(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_41(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_42(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_43(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_44(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_45(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_46(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_47(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_48(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_49(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_50(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_51(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_52(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_53(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_54(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_55(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_56(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_57(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_58(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_59(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_60(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_61(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_62(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_63(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_64(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_65(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_66(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_67(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_68(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_69(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_70(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_71(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_72(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_73(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_74(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_75(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_76(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_77(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_78(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_79(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_80(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_81(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_82(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_83(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_84(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_85(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_86(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_87(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_88(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_89(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_90(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_91(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_92(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_93(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_94(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_95(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_96(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_97(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_98(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_99(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_100(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_101(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}

method n_NI_Local_GetX_PutX__part__1inv__132_102(                          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















































requires 0<=src<N0

requires ((Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Local[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := true;
    Sta_Dir_HeadVld[0] := true;
    Sta_Dir_HeadPtr[0] := src;
    Sta_Dir_HomeHeadPtr[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_UniMsg_Cmd[src] := UNI_PutX;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    if ((Sta_Dir_HeadVld[0] == true) ==> ((((Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false)) && (forall p  |0<= p<N0 :: ((!(p == src)) ==> (Sta_Dir_ShrSet[p] == false)) )) && (Sta_Dir_HomeShrSet[0] == false))) {
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        Sta_Dir_InvSet[p] := false;
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      Sta_HomeProc_CacheState[0] := CACHE_I;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }}
else{
      Sta_Dir_Pending[0] := true;
      Sta_Dir_Local[0] := false;
      Sta_Dir_Dirty[0] := true;
      Sta_Dir_HeadVld[0] := true;
      Sta_Dir_HeadPtr[0] := src;
      Sta_Dir_HomeHeadPtr[0] := false;
      Sta_Dir_ShrVld[0] := false;
      forall p  |0<= p<N0 {
        Sta_Dir_ShrSet[p] := false;
        if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
          Sta_Dir_InvSet[p] := true;
          Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
          Sta_Dir_InvSet[p] := false;
          Sta_InvMsg_Cmd[p] := INV_None;
        }
      }
      Sta_Dir_HomeShrSet[0] := false;
      Sta_Dir_HomeInvSet[0] := false;
      Sta_HomeInvMsg_Cmd[0] := INV_None;
      Sta_UniMsg_Cmd[src] := UNI_PutX;
      if (Sta_Dir_Local[0] == true) {
        Sta_HomeProc_CacheState[0] := CACHE_I;
        if (Sta_HomeProc_ProcCmd[0] == NODE_Get) {
          Sta_HomeProc_InvMarked[0] := true;
        }
      }
    }
  }
}



method n_PI_Local_Get_Put()
requires 

requires (Sta_HomeProc_InvMarked[0] == true)//branch
//case 1//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_I) && (Sta_HomeProc_ProcCmd[0] == NODE_None));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd{
  Sta_Dir_Local[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  if (Sta_HomeProc_InvMarked[0] == true) {
    Sta_HomeProc_InvMarked[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_S;
  }
}

method n_PI_Local_Get_Put()
requires 

requires (!(Sta_HomeProc_InvMarked[0] == true))//branch
//case 1//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_I) && (Sta_HomeProc_ProcCmd[0] == NODE_None));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd{
  Sta_Dir_Local[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  if (Sta_HomeProc_InvMarked[0] == true) {
    Sta_HomeProc_InvMarked[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_S;
  }
}


method n_PI_Local_GetX_PutX__part__0()
requires 

requires (Sta_Dir_HeadVld[0] == true)//branch
//case 1//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_I));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  if (Sta_Dir_HeadVld[0] == true) {
    Sta_Dir_Pending[0] := true;
    Sta_Dir_HeadVld[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      if (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false))) {
        Sta_Dir_InvSet[p] := true;
        Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
        Sta_Dir_InvSet[p] := false;
        Sta_InvMsg_Cmd[p] := INV_None;
      }
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_HomeInvMsg_Cmd[0] := INV_None;
  }
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}

method n_PI_Local_GetX_PutX__part__0()
requires 

requires (!(Sta_Dir_HeadVld[0] == true))//branch
//case 1//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_I));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  if (Sta_Dir_HeadVld[0] == true) {
    Sta_Dir_Pending[0] := true;
    Sta_Dir_HeadVld[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      if (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false))) {
        Sta_Dir_InvSet[p] := true;
        Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
        Sta_Dir_InvSet[p] := false;
        Sta_InvMsg_Cmd[p] := INV_None;
      }
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_HomeInvMsg_Cmd[0] := INV_None;
  }
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}


method n_PI_Local_GetX_PutX__part__1()
requires 

requires (Sta_Dir_HeadVld[0] == true)//branch
//case 1//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_S));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  if (Sta_Dir_HeadVld[0] == true) {
    Sta_Dir_Pending[0] := true;
    Sta_Dir_HeadVld[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      if (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false))) {
        Sta_Dir_InvSet[p] := true;
        Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
        Sta_Dir_InvSet[p] := false;
        Sta_InvMsg_Cmd[p] := INV_None;
      }
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_HomeInvMsg_Cmd[0] := INV_None;
  }
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}

method n_PI_Local_GetX_PutX__part__1()
requires 

requires (!(Sta_Dir_HeadVld[0] == true))//branch
//case 1//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_S));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  if (Sta_Dir_HeadVld[0] == true) {
    Sta_Dir_Pending[0] := true;
    Sta_Dir_HeadVld[0] := false;
    Sta_Dir_ShrVld[0] := false;
    forall p  |0<= p<N0 {
      Sta_Dir_ShrSet[p] := false;
      if (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false))) {
        Sta_Dir_InvSet[p] := true;
        Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
        Sta_Dir_InvSet[p] := false;
        Sta_InvMsg_Cmd[p] := INV_None;
      }
    }
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
    Sta_HomeInvMsg_Cmd[0] := INV_None;
  }
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}


method n_PI_Local_PutX()
requires 

requires (Sta_Dir_Pending[0] == true)//branch
//case 1//guard condition
requires   ((Sta_HomeProc_CacheState[0] == CACHE_E) && (Sta_HomeProc_ProcCmd[0] == NODE_None));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState{
  if (Sta_Dir_Pending[0] == true) {
    Sta_HomeProc_CacheState[0] := CACHE_I;
    Sta_Dir_Dirty[0] := false;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_I;
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := false;
  }
}

method n_PI_Local_PutX()
requires 

requires (!(Sta_Dir_Pending[0] == true))//branch
//case 1//guard condition
requires   ((Sta_HomeProc_CacheState[0] == CACHE_E) && (Sta_HomeProc_ProcCmd[0] == NODE_None));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState{
  if (Sta_Dir_Pending[0] == true) {
    Sta_HomeProc_CacheState[0] := CACHE_I;
    Sta_Dir_Dirty[0] := false;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_I;
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := false;
  }
}


method n_PI_Local_Replace()
requires 

//case 1//guard condition
requires   ((Sta_HomeProc_CacheState[0] == CACHE_S) && (Sta_HomeProc_ProcCmd[0] == NODE_None));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState{
  Sta_Dir_Local[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Local_Put()
requires 

requires (Sta_HomeProc_InvMarked[0] == true)//branch
//case 1//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_Put);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_Local[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  if (Sta_HomeProc_InvMarked[0] == true) {
    Sta_HomeProc_InvMarked[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_S;
  }
}

method n_NI_Local_Put()
requires 

requires (!(Sta_HomeProc_InvMarked[0] == true))//branch
//case 1//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_Put);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_Local[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  if (Sta_HomeProc_InvMarked[0] == true) {
    Sta_HomeProc_InvMarked[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_S;
  }
}


method n_NI_Local_PutXAcksDone()
requires 

//case 1//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_PutX);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadVld
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Local[0] := true;
  Sta_Dir_HeadVld[0] := false;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}


method n_NI_Wb()
requires 

//case 1//guard condition
requires   (Sta_WbMsg_Cmd[0] == WB_Wb);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadVld
modifies Sta_WbMsg_Cmd{
  Sta_WbMsg_Cmd[0] := WB_None;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_HeadVld[0] := false;
}

method n_NI_Local_Get_Get__part__1inv__132_0(             
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




























requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc
{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_Get;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}


method n_NI_Remote_GetX_PutX_Homeinv__132_0(        
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_GetX) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (Sta_Proc_CacheState[dst] == CACHE_E)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_Proc_CacheState
{
  Sta_Proc_CacheState[dst] := CACHE_I;
  Sta_HomeUniMsg_Cmd[0] := UNI_PutX;
}


method n_PI_Remote_Getinv__132_0(        
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=src<N0

requires ((Sta_Proc_CacheState[src] == CACHE_I) && (Sta_Proc_ProcCmd[src] == NODE_None)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
{
  Sta_Proc_ProcCmd[src] := NODE_Get;
  Sta_UniMsg_Cmd[src] := UNI_Get;
  Sta_UniMsg_HomeProc[src] := true;
}


method n_NI_Local_GetX_GetX__part__1inv__132_0(            
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


























requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc
{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_GetX;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}



method n_PI_Local_GetX_GetX__part__1()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_S));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
modifies Sta_HomeUniMsg_HomeProc
modifies Sta_HomeUniMsg_Proc{
  Sta_HomeProc_ProcCmd[0] := NODE_GetX;
  Sta_Dir_Pending[0] := true;
  Sta_HomeUniMsg_Cmd[0] := UNI_GetX;
  Sta_HomeUniMsg_Proc[0] := Sta_Dir_HeadPtr[0];
  Sta_HomeUniMsg_HomeProc[0] := Sta_Dir_HomeHeadPtr[0];
}


method n_PI_Local_GetX_GetX__part__0()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_I));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
modifies Sta_HomeUniMsg_HomeProc
modifies Sta_HomeUniMsg_Proc{
  Sta_HomeProc_ProcCmd[0] := NODE_GetX;
  Sta_Dir_Pending[0] := true;
  Sta_HomeUniMsg_Cmd[0] := UNI_GetX;
  Sta_HomeUniMsg_Proc[0] := Sta_Dir_HeadPtr[0];
  Sta_HomeUniMsg_HomeProc[0] := Sta_Dir_HomeHeadPtr[0];
}

method n_PI_Remote_Replaceinv__132_0(       
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)
















requires 0<=src<N0

requires ((Sta_Proc_CacheState[src] == CACHE_S) && (Sta_Proc_ProcCmd[src] == NODE_None)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_CacheState
modifies Sta_RpMsg_Cmd
{
  Sta_Proc_CacheState[src] := CACHE_I;
  Sta_RpMsg_Cmd[src] := RP_Replace;
}


method n_NI_Local_GetX_Nak__part__1inv__132_0(          
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == false))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Local_Get_Nak__part__1inv__132_0(           
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)
























requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == false))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Local_Get_Get__part__0inv__132_0(             
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




























requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc
{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_Get;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}


method n_NI_Local_GetX_Nak__part__2inv__132_0(        
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == true) && (!(Sta_HomeProc_CacheState[0] == CACHE_E)))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_PI_Remote_PutXinv__132_0(         
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




















requires 0<=dst<N0

requires ((Sta_Proc_CacheState[dst] == CACHE_E) && (Sta_Proc_ProcCmd[dst] == NODE_None)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_CacheState
modifies Sta_WbMsg_Cmd
modifies Sta_WbMsg_HomeProc
modifies Sta_WbMsg_Proc
{
  Sta_Proc_CacheState[dst] := CACHE_I;
  Sta_WbMsg_Cmd[0] := WB_Wb;
  Sta_WbMsg_Proc[0] := dst;
  Sta_WbMsg_HomeProc[0] := false;
}


method n_NI_Remote_Get_Put_Homeinv__132_0(        
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (Sta_Proc_CacheState[dst] == CACHE_E)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_Proc_CacheState
{
  Sta_Proc_CacheState[dst] := CACHE_S;
  Sta_HomeUniMsg_Cmd[0] := UNI_Put;
}


method n_NI_InvAckinv__132_0(               
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)
































requires 0<=src<N0

requires ((Sta_Dir_InvSet[src] == true) && (Sta_Dir_Pending[0] == true) && (Sta_InvMsg_Cmd[src] == INV_InvAck)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_InvMsg_Cmd
{
  Sta_InvMsg_Cmd[src] := INV_None;
  Sta_Dir_InvSet[src] := false;
  if ((!(exists p  |0<= p<N0 :: ((!(p == src)) && (Sta_Dir_InvSet[p] == true)))) && (Sta_Dir_HomeInvSet[0] == false)) {
    Sta_Dir_Pending[0] := false;
    if ((Sta_Dir_Local[0] == true) && (Sta_Dir_Dirty[0] == false)) {
      Sta_Dir_Local[0] := false;
    }
  }
}


method n_NI_Invinv__132_0(        
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=dst<N0

requires (Sta_InvMsg_Cmd[dst] == INV_Inv) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_InvMsg_Cmd
modifies Sta_Proc_CacheState
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
{
  Sta_InvMsg_Cmd[dst] := INV_InvAck;
  Sta_Proc_CacheState[dst] := CACHE_I;
  if (Sta_Proc_ProcCmd[dst] == NODE_Get) {
    Sta_Proc_InvMarked[dst] := true;
  }
}


method n_NI_Local_Get_Nak__part__2inv__132_0(         
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




















requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == true) && (!(Sta_HomeProc_CacheState[0] == CACHE_E)))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Local_GetX_GetX__part__0inv__132_0(            
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


























requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc
{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_GetX;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}



method n_NI_ShWb()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (Sta_ShWbMsg_Cmd[0] == SHWB_ShWb);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc{
  Sta_ShWbMsg_Cmd[0] := SHWB_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_ShrVld[0] := true;
  forall p  |0<= p<N0 {
    if (((p == Sta_ShWbMsg_Proc[0]) && (Sta_ShWbMsg_HomeProc[0] == false)) || (Sta_Dir_ShrSet[p] == true)) {
      Sta_Dir_ShrSet[p] := true;
      Sta_Dir_InvSet[p] := true;}
else{
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
  }
  if ((Sta_ShWbMsg_HomeProc[0] == true) || (Sta_Dir_HomeShrSet[0] == true)) {
    Sta_Dir_HomeShrSet[0] := true;
    Sta_Dir_HomeInvSet[0] := true;}
else{
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
  }
}

method n_NI_Replaceinv__132_0(        
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=src<N0

requires (Sta_RpMsg_Cmd[src] == RP_Replace) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_RpMsg_Cmd
{
  Sta_RpMsg_Cmd[src] := RP_None;
  if (Sta_Dir_ShrVld[0] == true) {
    Sta_Dir_ShrSet[src] := false;
    Sta_Dir_InvSet[src] := false;
  }
}


method n_NI_Remote_GetX_Nak_Homeinv__132_0(         
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




















requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_GetX) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_NakcMsg_Cmd
{
  Sta_HomeUniMsg_Cmd[0] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Remote_GetX_Nakinv__132_0(          
src:nat, N0:nat,dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E)) && (!(src == dst))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_NakcMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Nakinv__132_0(       
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)
















requires 0<=dst<N0

requires (Sta_UniMsg_Cmd[dst] == UNI_Nak) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[dst] := UNI_None;
  Sta_Proc_ProcCmd[dst] := NODE_None;
  Sta_Proc_InvMarked[dst] := false;
}


method n_PI_Remote_GetXinv__132_0(        
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=src<N0

requires ((Sta_Proc_CacheState[src] == CACHE_I) && (Sta_Proc_ProcCmd[src] == NODE_None)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
{
  Sta_Proc_ProcCmd[src] := NODE_GetX;
  Sta_UniMsg_Cmd[src] := UNI_GetX;
  Sta_UniMsg_HomeProc[src] := true;
}


method n_NI_Remote_Get_Nak_Homeinv__132_0(         
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)




















requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_NakcMsg_Cmd
{
  Sta_HomeUniMsg_Cmd[0] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Remote_PutXinv__132_0(        
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=dst<N0

requires ((Sta_Proc_ProcCmd[dst] == NODE_GetX) && (Sta_UniMsg_Cmd[dst] == UNI_PutX)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_CacheState
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[dst] := UNI_None;
  Sta_Proc_ProcCmd[dst] := NODE_None;
  Sta_Proc_InvMarked[dst] := false;
  Sta_Proc_CacheState[dst] := CACHE_E;
}


method n_NI_Remote_Putinv__132_0(        
dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=dst<N0

requires (Sta_UniMsg_Cmd[dst] == UNI_Put) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_CacheState
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[dst] := UNI_None;
  Sta_Proc_ProcCmd[dst] := NODE_None;
  if (Sta_Proc_InvMarked[dst] == true) {
    Sta_Proc_InvMarked[dst] := false;
    Sta_Proc_CacheState[dst] := CACHE_I;}
else{
    Sta_Proc_CacheState[dst] := CACHE_S;
  }
}


method n_NI_Local_GetX_Nak__part__0inv__132_0(       
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)
















requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (Sta_Dir_Pending[0] == true)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}



method n_NI_Replace_Home()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (Sta_HomeRpMsg_Cmd[0] == RP_Replace);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeRpMsg_Cmd{
  Sta_HomeRpMsg_Cmd[0] := RP_None;
  if (Sta_Dir_ShrVld[0] == true) {
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
  }
}

method n_NI_Remote_GetX_PutXinv__132_0(            
src:nat, N0:nat,dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


























requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_Proc_CacheState[dst] == CACHE_E) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(src == dst))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_CacheState
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc
modifies Sta_UniMsg_Cmd
{
  Sta_Proc_CacheState[dst] := CACHE_I;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_ShWbMsg_Cmd[0] := SHWB_FAck;
  Sta_ShWbMsg_Proc[0] := src;
  Sta_ShWbMsg_HomeProc[0] := false;
}


method n_NI_Remote_Get_Nakinv__132_0(          
src:nat, N0:nat,dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)






















requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E)) && (!(src == dst))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_NakcMsg_Cmd
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}



method n_NI_Nak_Clear()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (Sta_NakcMsg_Cmd[0] == NAKC_Nakc);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Pending
modifies Sta_NakcMsg_Cmd{
  Sta_NakcMsg_Cmd[0] := NAKC_None;
  Sta_Dir_Pending[0] := false;
}

method n_NI_Local_Get_Nak__part__0inv__132_0(        
src:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


















requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (Sta_Dir_Pending[0] == true)) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_UniMsg_Cmd
{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}



method n_PI_Local_Get_Get()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_I) && (Sta_HomeProc_ProcCmd[0] == NODE_None));
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
modifies Sta_HomeUniMsg_HomeProc
modifies Sta_HomeUniMsg_Proc{
  Sta_HomeProc_ProcCmd[0] := NODE_Get;
  Sta_Dir_Pending[0] := true;
  Sta_HomeUniMsg_Cmd[0] := UNI_Get;
  Sta_HomeUniMsg_Proc[0] := Sta_Dir_HeadPtr[0];
  Sta_HomeUniMsg_HomeProc[0] := Sta_Dir_HomeHeadPtr[0];
}

method n_NI_Remote_Get_Putinv__132_0(            
src:nat, N0:nat,dst:nat, N0:nat,p__Inv0:nat,p__Inv2:nat)


























requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_Proc_CacheState[dst] == CACHE_E) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(src == dst))) //guard condition
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Proc_CacheState
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc
modifies Sta_UniMsg_Cmd
{
  Sta_Proc_CacheState[dst] := CACHE_S;
  Sta_UniMsg_Cmd[src] := UNI_Put;
  Sta_ShWbMsg_Cmd[0] := SHWB_ShWb;
  Sta_ShWbMsg_Proc[0] := src;
  Sta_ShWbMsg_HomeProc[0] := false;
}



method n_NI_Nak_Home()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_Nak);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
}


method n_NI_FAck()
requires 
requires (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (Sta_ShWbMsg_Cmd[0] == SHWB_FAck);
ensures (!((Sta_Dir_HeadVld[0] == true) && (Sta_HomeProc_CacheState[0] == CACHE_E)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc{
  Sta_ShWbMsg_Cmd[0] := SHWB_None;
  Sta_Dir_Pending[0] := false;
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_HeadPtr[0] := Sta_ShWbMsg_Proc[0];
    Sta_Dir_HomeHeadPtr[0] := Sta_ShWbMsg_HomeProc[0];
  }
}

