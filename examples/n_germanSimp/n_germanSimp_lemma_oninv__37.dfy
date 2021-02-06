datatype CACHE_STATE = I| S| E
datatype MSG_CMD = Empty| ReqS| ReqE| Inv| InvAck| GntS| GntE
type NODE=nat
type DATA=nat
type boolean=bool




method n_Storeinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_5(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_6(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_7(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_8(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__37_9(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, ShrSet:array<boolean>,
N0:nat,i:nat,d:nat,N1:nat,
p__Inv4:nat)
requires N0>0
requires N1>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires 0<=d<N1
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (ShrSet[p__Inv4] == true)))//3
requires (Cache_State[i] == E) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies AuxData
modifies Cache_Data

{
  Cache_Data[i] := d;
  AuxData[0] := d;
}


method n_SendInv__part__0inv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && (CurCmd[0] == ReqE)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__0inv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && (CurCmd[0] == ReqE)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__0inv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && (CurCmd[0] == ReqE)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__0inv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && (CurCmd[0] == ReqE)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__0inv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && (CurCmd[0] == ReqE)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}


method n_SendInv__part__1inv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && ((CurCmd[0] == ReqS) && (ExGntd[0] == true))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__1inv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && ((CurCmd[0] == ReqS) && (ExGntd[0] == true))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__1inv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && ((CurCmd[0] == ReqS) && (ExGntd[0] == true))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__1inv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && ((CurCmd[0] == ReqS) && (ExGntd[0] == true))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}

method n_SendInv__part__1inv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, InvSet:array<boolean>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires InvSet.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && ((CurCmd[0] == ReqS) && (ExGntd[0] == true))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies InvSet

{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}


method n_SendInvAckinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]
requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
requires (!((Chan2_Cmd[p__Inv4] == Inv) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//3
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data

{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}

method n_SendInvAckinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]
requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data

{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}

method n_SendInvAckinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]
requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data

{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}

method n_SendInvAckinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]
requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data

{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}

method n_SendInvAckinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]
requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data

{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}


method n_RecvInvAckinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>,  Chan3_Data:array<DATA>, CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0

requires Chan3_Data.Length==N0
requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]

requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((Chan3_Cmd[i] == InvAck) && (!(CurCmd[0] == Empty))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan3_Cmd
modifies Chan3_Data
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan3_Cmd[i] := Empty;
  ShrSet[i] := false;
  if (ExGntd[0] == true) {
    ExGntd[0] := false;
    MemData[0] := Chan3_Data[i];
  }
}

method n_RecvInvAckinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>,  Chan3_Data:array<DATA>, CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0

requires Chan3_Data.Length==N0
requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]

requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan3_Cmd[i] == InvAck) && (!(CurCmd[0] == Empty))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan3_Cmd
modifies Chan3_Data
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan3_Cmd[i] := Empty;
  ShrSet[i] := false;
  if (ExGntd[0] == true) {
    ExGntd[0] := false;
    MemData[0] := Chan3_Data[i];
  }
}

method n_RecvInvAckinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>,  Chan3_Data:array<DATA>, CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0

requires Chan3_Data.Length==N0
requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]

requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan3_Cmd[i] == InvAck) && (!(CurCmd[0] == Empty))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan3_Cmd
modifies Chan3_Data
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan3_Cmd[i] := Empty;
  ShrSet[i] := false;
  if (ExGntd[0] == true) {
    ExGntd[0] := false;
    MemData[0] := Chan3_Data[i];
  }
}

method n_RecvInvAckinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>,  Chan3_Data:array<DATA>, CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0

requires Chan3_Data.Length==N0
requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]

requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan3_Cmd[i] == InvAck) && (!(CurCmd[0] == Empty))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan3_Cmd
modifies Chan3_Data
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan3_Cmd[i] := Empty;
  ShrSet[i] := false;
  if (ExGntd[0] == true) {
    ExGntd[0] := false;
    MemData[0] := Chan3_Data[i];
  }
}

method n_RecvInvAckinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>,  Chan3_Data:array<DATA>, CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0

requires Chan3_Data.Length==N0
requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan3_Cmd.Length&&0<=j<Chan3_Cmd.Length==>Chan3_Cmd[i]!=Chan3_Cmd[j]

requires forall i,j::0<=i<Chan3_Data.Length&&0<=j<Chan3_Data.Length==>Chan3_Data[i]!=Chan3_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan3_Cmd[i] == InvAck) && (!(CurCmd[0] == Empty))) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan3_Cmd
modifies Chan3_Data
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan3_Cmd[i] := Empty;
  ShrSet[i] := false;
  if (ExGntd[0] == true) {
    ExGntd[0] := false;
    MemData[0] := Chan3_Data[i];
  }
}


method n_SendGntSinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqS) && (CurPtr[0] == i) && (ExGntd[0] == false)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntS;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  CurCmd[0] := Empty;
}

method n_SendGntSinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqS) && (CurPtr[0] == i) && (ExGntd[0] == false)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntS;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  CurCmd[0] := Empty;
}

method n_SendGntSinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqS) && (CurPtr[0] == i) && (ExGntd[0] == false)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntS;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  CurCmd[0] := Empty;
}

method n_SendGntSinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqS) && (CurPtr[0] == i) && (ExGntd[0] == false)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntS;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  CurCmd[0] := Empty;
}

method n_SendGntSinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqS) && (CurPtr[0] == i) && (ExGntd[0] == false)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntS;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  CurCmd[0] := Empty;
}


method n_SendGntEinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,     
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0





requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]





requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqE) && (CurPtr[0] == i) && (ExGntd[0] == false) && (forall j  |0<= j<N0 :: (ShrSet[j] == false) )) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntE;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  ExGntd[0] := true;
  CurCmd[0] := Empty;
}

method n_SendGntEinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,     
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0





requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]





requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqE) && (CurPtr[0] == i) && (ExGntd[0] == false) && (forall j  |0<= j<N0 :: (ShrSet[j] == false) )) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntE;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  ExGntd[0] := true;
  CurCmd[0] := Empty;
}

method n_SendGntEinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,     
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0





requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]





requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqE) && (CurPtr[0] == i) && (ExGntd[0] == false) && (forall j  |0<= j<N0 :: (ShrSet[j] == false) )) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntE;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  ExGntd[0] := true;
  CurCmd[0] := Empty;
}

method n_SendGntEinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,     
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0





requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]





requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqE) && (CurPtr[0] == i) && (ExGntd[0] == false) && (forall j  |0<= j<N0 :: (ShrSet[j] == false) )) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntE;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  ExGntd[0] := true;
  CurCmd[0] := Empty;
}

method n_SendGntEinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,     
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0





requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]

requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<ExGntd.Length&&0<=j<ExGntd.Length==>ExGntd[i]!=ExGntd[j]
requires forall i,j::0<=i<MemData.Length&&0<=j<MemData.Length==>MemData[i]!=MemData[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]





requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqE) && (CurPtr[0] == i) && (ExGntd[0] == false) && (forall j  |0<= j<N0 :: (ShrSet[j] == false) )) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies ExGntd
modifies MemData
modifies ShrSet

{
  Chan2_Cmd[i] := GntE;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  ExGntd[0] := true;
  CurCmd[0] := Empty;
}


method n_RecvGntSinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
requires (!((Chan2_Cmd[p__Inv4] == GntS) && (!(Chan2_Data[p__Inv4] == AuxData[0]))))//3
requires (Chan2_Cmd[i] == GntS) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntSinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntS) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntSinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntS) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntSinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntS) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntSinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntS) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}


method n_RecvGntEinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
requires (!((Chan2_Cmd[p__Inv4] == GntE) && (!(Chan2_Data[p__Inv4] == AuxData[0]))))//3
requires (Chan2_Cmd[i] == GntE) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntEinv__37_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntE) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntEinv__37_2(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntE) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntEinv__37_3(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntE) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntEinv__37_4(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>, ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]


requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]
requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<Chan2_Data.Length&&0<=j<Chan2_Data.Length==>Chan2_Data[i]!=Chan2_Data[j]
requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//2
requires (Chan2_Cmd[i] == GntE) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data

{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}


method n_RecvReqE__part__0inv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>,  Chan2_Cmd:array<MSG_CMD>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, InvSet:array<boolean>,  ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0

requires Chan2_Cmd.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires InvSet.Length==N0

requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]

requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//statement has nothing with prop--it guranttee itself

requires ((CurCmd[0] == Empty) && (Cache_State[i] == I)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies CurCmd
modifies CurPtr
modifies InvSet
modifies ShrSet

{
  CurCmd[0] := ReqE;
  CurPtr[0] := i;
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    InvSet[j] := ShrSet[j];
  
 j:=j+1;
}
}


method n_RecvReqE__part__1inv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>,  Chan2_Cmd:array<MSG_CMD>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, InvSet:array<boolean>,  ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0

requires Chan2_Cmd.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires InvSet.Length==N0

requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]

requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//statement has nothing with prop--it guranttee itself

requires ((CurCmd[0] == Empty) && (Cache_State[i] == S)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies CurCmd
modifies CurPtr
modifies InvSet
modifies ShrSet

{
  CurCmd[0] := ReqE;
  CurPtr[0] := i;
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    InvSet[j] := ShrSet[j];
  
 j:=j+1;
}
}


method n_RecvReqSinv__37_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>,  Chan2_Cmd:array<MSG_CMD>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, InvSet:array<boolean>,  ShrSet:array<boolean>,
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0

requires Chan2_Cmd.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires InvSet.Length==N0

requires ShrSet.Length==N0
requires forall i,j::0<=i<AuxData.Length&&0<=j<AuxData.Length==>AuxData[i]!=AuxData[j]


requires forall i,j::0<=i<Cache_Data.Length&&0<=j<Cache_Data.Length==>Cache_Data[i]!=Cache_Data[j]

requires forall i,j::0<=i<Cache_State.Length&&0<=j<Cache_State.Length==>Cache_State[i]!=Cache_State[j]

requires forall i,j::0<=i<Chan2_Cmd.Length&&0<=j<Chan2_Cmd.Length==>Chan2_Cmd[i]!=Chan2_Cmd[j]
requires forall i,j::0<=i<CurCmd.Length&&0<=j<CurCmd.Length==>CurCmd[i]!=CurCmd[j]
requires forall i,j::0<=i<CurPtr.Length&&0<=j<CurPtr.Length==>CurPtr[i]!=CurPtr[j]
requires forall i,j::0<=i<InvSet.Length&&0<=j<InvSet.Length==>InvSet[i]!=InvSet[j]

requires forall i,j::0<=i<ShrSet.Length&&0<=j<ShrSet.Length==>ShrSet[i]!=ShrSet[j]
requires 0<=i<N0
requires  p__Inv4<N0
requires (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))//statement has nothing with prop--it guranttee itself

requires ((Cache_State[i] == I) && (CurCmd[0] == Empty)) //guard condition
ensures   (!((!(Cache_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == Empty) && (ShrSet[p__Inv4] == true)))
modifies CurCmd
modifies CurPtr
modifies InvSet
modifies ShrSet

{
  CurCmd[0] := ReqS;
  CurPtr[0] := i;
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    InvSet[j] := ShrSet[j];
  
 j:=j+1;
}
}


