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

HomeProc : boolean,

Proc : NODE,

Cmd : WB_CMD

}

 

 

class  class_3  {

var

Cmd : RP_CMD

}

 

 

class  class_4  {

var

Cmd : INV_CMD

}

 

 

class  class_5  {

var

HomeProc : boolean,

Proc : NODE,

Cmd : UNI_CMD

}

 

 

class  class_6  {

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

 

 

class  class_7  {

var

CacheState : CACHE_STATE,

InvMarked : boolean,

ProcCmd : NODE_CMD

}

 

 

class  class_8  {

var

NakcMsg : class_0 ,

ShWbMsg : class_1 ,

WbMsg : class_2 ,

HomeRpMsg : class_3 ,

RpMsg : array<class_3 >,

HomeInvMsg : class_4 ,

InvMsg : array<class_4 >,

HomeUniMsg : class_5 ,

UniMsg : array<class_5 >,

Dir : class_6 ,

HomeProc : class_7 ,

Proc : array<class_7 >;

constructor(invmsg:array<class_4 >,unimsg:array<class_5 >,rpmsg:array<class_3 >,proc:array<class_7 >){

NakcMsg := new class_0 ;

ShWbMsg := new class_1 ;

WbMsg := new class_2 ;

HomeRpMsg := new class_3 ;

RpMsg := rpmsg;

HomeInvMsg := new class_4 ;

InvMsg := invmsg;

HomeUniMsg := new class_5 ;

UniMsg := unimsg;

Dir := new class_6 ;

HomeProc := new class_7 ;

Proc := proc;

}

}

 

 

class TopC{

var

Sta : class_8 ;

constructor (){

var

invmsg:array<class_4 >,unimsg:array<class_5 >,rpmsg:array<class_3 >,proc:array<class_7 >;

Sta := new class_8

(invmsg, unimsg, rpmsg, proc);

}

}

 

method n_NI_ShWbinv__4_0(top:TopC,N0:nat,p__Inv4:nat)

//requires top!=null

//requires top.Sta!=null

//requires top.Sta.Dir!=null

requires N0>0

requires top.Sta.Dir.InvSet.Length==N0

ensures top.Sta.Dir.InvSet==old(top.Sta.Dir.InvSet)

 

requires N0>0

requires top.Sta.Dir.ShrSet.Length==N0

ensures top.Sta.Dir.ShrSet==old(top.Sta.Dir.ShrSet)

//ensures top.Sta.Dir==old(top.Sta.Dir)

requires N0>0

requires top.Sta.UniMsg.Length==N0

requires forall i,j::0<=i<top.Sta.UniMsg.Length&&0<=j<top.Sta.UniMsg.Length==>top.Sta.UniMsg[i]!=top.Sta.UniMsg[j]

// ensures top.Sta.UniMsg==old(top.Sta.UniMsg)top.Sta.Dir.HomeShrSet

requires forall i::0<=i<top.Sta.Dir.ShrSet.Length

==>top.Sta.Dir.ShrSet[i]!=top.Sta.Dir.HomeShrSet

 

requires  p__Inv4<N0

requires (!((top.Sta.HomeProc.CacheState == CACHE_E) && (top.Sta.UniMsg[p__Inv4].Cmd == UNI_PutX)))//statement has nothing with prop--it guranttee itself

//guard condition

requires   (top.Sta.ShWbMsg.Cmd == SHWB_ShWb);

// ensures   (!((top.Sta.HomeProc.CacheState == CACHE_E) && (top.Sta.UniMsg[p__Inv4].Cmd == UNI_PutX)))

modifies top.Sta.Dir.InvSet

modifies top.Sta.Dir.ShrSet

modifies top.Sta.Dir

modifies top.Sta.ShWbMsg

modifies top.Sta

modifies top

 

{

  top.Sta.ShWbMsg.Cmd := SHWB_None;

  top.Sta.Dir.Pending := false;

  top.Sta.Dir.Dirty := false;

  top.Sta.Dir.ShrVld := true;

 

  var p:=0;

  while(p<N0)

    decreases N0-p

    invariant top.Sta.Dir.ShrSet==old(top.Sta.Dir.ShrSet)

    invariant top.Sta.Dir.InvSet==old(top.Sta.Dir.InvSet)

  {  //assume 0<p<=top.Sta.Dir.ShrSet.Length;

     //assume 0<p<=top.Sta.Dir.InvSet.Length;

     aux1(p,N0,top.Sta.Dir.ShrSet.Length);

     aux1(p,N0,top.Sta.Dir.InvSet.Length);

      if (((p == top.Sta.ShWbMsg.Proc) && (top.Sta.ShWbMsg.HomeProc == false)) || (top.Sta.Dir.ShrSet[p] == true)) {

        top.Sta.Dir.ShrSet[p] := true;

        top.Sta.Dir.InvSet[p] := true;}

  else{

        top.Sta.Dir.ShrSet[p] := false;

        top.Sta.Dir.InvSet[p] := false;

      }

  p:=p+1;

  }

  //assert top==old(top);

// assert top.Sta ==old(top.Sta );

  //assert top.Sta.Dir==old(top.Sta.Dir);

  if ((top.Sta.ShWbMsg.HomeProc == true) || (top.Sta.Dir.HomeShrSet == true)){

    top.Sta.Dir.HomeShrSet := true;

    top.Sta.Dir.HomeInvSet := true;}

  else{

    //top.Sta.Dir.HomeShrSet := false;

    top.Sta.Dir.HomeInvSet := false;

  }

 

}

 

lemma aux1(p:int, N0: int, M:int)

requires 0<=p<N0

requires N0==M

ensures 0<=p<M

{}