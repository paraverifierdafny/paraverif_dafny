type role = string
datatype message = Nil | Aenc(aencMsg:message,aencKey:message) | Senc(m1:message,m2:message) | K(r1:role,r2:role) | Pk(r:role) | Sk(r:role) | Str(r:role) | Var(n:role) | Pair(m1:message,m2:message)
type channel = array<message>
method aencrtpy(aencMsg:message,aencKey:message,intruKnows:set<message>) returns (newIntruKnows:set<message>)
    requires aencMsg in intruKnows
    requires aencKey in intruKnows
    requires Aenc(aencMsg,aencKey) !in intruKnows
    ensures Aenc(aencMsg,aencKey) in newIntruKnows
    {
        var aencMsg1:=Aenc(aencMsg,aencKey);
        newIntruKnows:=intruKnows+{aencMsg1};
    }
method dencrtpy(msg:message,aencKey:message,aencMsg:message,intruKnows:set<message>) returns (newIntruKnows:set<message>)
    requires msg in intruKnows
    requires aencKey in intruKnows
    requires aencMsg != Var("Na")
    requires aencMsg !in intruKnows
    requires msg == Aenc(aencMsg,aencKey)
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in newIntruKnows
    ensures aencMsg in newIntruKnows
    {
        newIntruKnows:=intruKnows+{aencMsg};
    }
method sencrtpy(sencMsg:message,sencKey:message,intruKnows:set<message>) returns (newIntruKnows:set<message>)
    requires sencMsg in intruKnows
    requires sencKey in intruKnows
    requires Senc(sencMsg,sencKey) !in intruKnows
    ensures Senc(sencMsg,sencKey) in newIntruKnows
    {
        var sencMsg1:=Senc(sencMsg,sencKey);
        newIntruKnows:=intruKnows+{sencMsg1};
    }
method dsencrtpy(msg:message,sencKey:message,sencMsg:message,intruKnows:set<message>) returns (newIntruKnows:set<message>)
    requires msg in intruKnows
    requires sencKey in intruKnows
    requires sencMsg !in intruKnows
    requires msg == Senc(sencMsg,sencKey)
    requires sencMsg != Var("Na")
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in newIntruKnows
    ensures sencMsg in newIntruKnows
    {
        newIntruKnows:=intruKnows+{sencMsg};
    }
method destructPair(pairMsg:message,m1:message,m2:message,intruKnows:set<message>)returns (newIntruKnows:set<message>)
    requires pairMsg in intruKnows
    requires pairMsg == Pair(m1,m2)
    requires m1 !in intruKnows || m2 !in intruKnows
    requires m1 != Var("Na") && m2 != Var("Na")
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in newIntruKnows
    ensures m1 in newIntruKnows && m2 in newIntruKnows
    {
        newIntruKnows:=intruKnows+{m1,m2};
    }
method constructPair(m1:message,m2:message,intruKnows:set<message>) returns (newIntruKnows:set<message>)
    requires m1 in intruKnows
    requires m2 in intruKnows
    requires Pair(m1,m2) !in intruKnows
    ensures Pair(m1,m2) in newIntruKnows
{ 
    newIntruKnows:=intruKnows+{Pair(m1,m2)};    
}
method ReceiveMsgFromChannel(c:channel,m1:message,intruKnows:set<message>) returns (m:message)//take message from channel
    requires c.Length > 0 
    requires m1!=Nil  
    requires m1 == c[0]
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures m1 == m
    ensures c[0] == Nil
    modifies c
{
    c[0]:=Nil;
    m:=m1;
}
method SendMsgToChannel(c:channel,m:message,intruKnows:set<message>)//put the message into channel
    requires c.Length > 0 
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures  c[0] == m
    modifies c
{
    c[0] := m;
}
method AliceSendMsg_1(c:channel,intruKnows:set<message>)//Alice sends the first message into channel
    requires c.Length > 0
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures  c[0]!=Nil
    modifies c
{
    var aencMsg:=Pair(Var("Na"),Str("A")); 
    var m :=Aenc(aencMsg,Pk("B")); 
    c[0] := m;
}
method AliceSendMsg_2(c:channel,intruKnows:set<message>)//Alice sends the second message into channel
    requires c.Length > 0
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures c[0]!=Nil
    modifies c
{
    var aencMsg:=Var("Nb");
    var m :=Aenc(aencMsg,Pk("B"));
    c[0] :=m;
}
method BobSendMsg_1(c:channel,intruKnows:set<message>)//Bob sends the first message into channel
    requires c.Length > 0
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures c[0] != Nil
    modifies c
{
    var aencMsg:=Pair(Var("Na"),Var("Nb"));
    var m :=Aenc(aencMsg,Pk("A"));
    c[0] :=m;
}

 method AliceGetMsg_1(c:array<message>,intruKnows:set<message>,flag:bool) returns (m:message)//Alice receives the first message from channel
    requires c.Length > 0 
    requires flag == false
    requires rverify(c[0])
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
  method BobGetMsg_1(c:array<message>,intruKnows:set<message>) returns (m:message)//Bob receives the first message from channel
    requires c.Length > 0 
    requires rverify(c[0])
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
  method BobGetMsg_2(c:array<message>,intruKnows:set<message>) returns (m:message)//Bob receives the third message from channel
    requires c.Length > 0 
    requires rverify(c[0])
    requires Var("Na") !in intruKnows
    ensures Var("Na") !in intruKnows
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
method IntruderGetMsg(c:channel,intruKnows:set<message>,i:int) returns (newIntruKnows:set<message>)//intruder intercepts the message in channel and insert it into intruder knowledge databases.
    requires c.Length > 0
    requires iverify(c[0])
    // ensures Var("Na") !in intruKnows    // ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0] == Nil
    modifies c
{   
    var aencMsg := destruct(c[0]);
    newIntruKnows := intruKnows+{aencMsg,c[0]};
    c[0]:=Nil;
}
 
predicate  rverify(m:message)//Alice or Bob verify Message received
{
    match m
    case Nil => false
    case Aenc(aencMsg,aencKey) => if aencKey == message.Pk("B") || aencKey == message.Pk("A") then true  else false
    case Senc(m1,m2)=> false
    case Var(r1)=> false
    case Str(r1)=> false
    case Pk(r1) => false
    case Sk(r1) => false
    case K(r1,r2)=>false
    case Pair(m1,m2) => false
 }
predicate  iverify(m:message)//Intruder verify message received
{
    match m
    case Nil => false
    case Aenc(aencMsg,aencKey) => if aencKey == message.Pk("I") then true  else false
    case Senc(m1,m2)=> true
    case Var(r1)=> false
    case Str(r1)=> true
    case Pk(r1) => true
    case Sk(r1) => true
    case K(r1,r2)=>true
    case Pair(m1,m2) => true
 }

function method  destruct(m:message):message//Destruct the message into submessage
{
    match m
    case Nil => Nil
    case Aenc(aencMsg,aencKey) => if aencKey == message.Pk("I") then aencMsg  else Aenc(aencMsg,aencKey)
    case Senc(aencMsg,sencKey)=> Senc(aencMsg,sencKey)
    case Var(r1)=> Var(r1)
    case Str(r1)=> Str(r1)
    case Pk(r1) => Pk(r1)
    case Sk(r1) => Sk(r1)
    case K(r1,r2)=>K(r1,r2)
    case Pair(m1,m2) =>  Pair(m1,m2)
 }
method Main(){
    var n:=Var("Na");
    var c:=new message[1];
    var ik:= {n};
    AliceSendMsg_1(c,ik);
}