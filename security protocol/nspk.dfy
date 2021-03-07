type role = string
datatype message = Nil | Aenc(aencMsg:message,aencKey:message) | Senc(m1:message,m2:message) | K(r1:role,r2:role) | Pk(r:role) | Sk(r:role) | Str(r:role) | Var(n:role) | Pair(m1:message,m2:message)
type channel = array<message>
method aencrtpy(aencMsg:message,aencKey:message,advKnw:set<message>) returns (advKnw1:set<message>)
    requires aencMsg in advKnw
    requires aencKey in advKnw
    requires Aenc(aencMsg,aencKey) !in advKnw
    ensures Aenc(aencMsg,aencKey) in advKnw1
    {
        var aencMsg1:=Aenc(aencMsg,aencKey);
        advKnw1:=advKnw+{aencMsg1};
    }
method dencrtpy(msg:message,aencKey:message,aencMsg:message,advKnw:set<message>) returns (advKnw1:set<message>)
    requires msg in advKnw
    requires aencKey in advKnw
    requires aencMsg != Var("Nb")
    requires aencMsg !in advKnw
    requires msg == Aenc(aencMsg,aencKey)
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw1
    ensures aencMsg in advKnw1
    {
        advKnw1:=advKnw+{aencMsg};
    }
method sencrtpy(sencMsg:message,sencKey:message,advKnw:set<message>) returns (advKnw1:set<message>)
    requires sencMsg in advKnw
    requires sencKey in advKnw
    requires Senc(sencMsg,sencKey) !in advKnw
    ensures Senc(sencMsg,sencKey) in advKnw1
    {
        var sencMsg1:=Senc(sencMsg,sencKey);
        advKnw1:=advKnw+{sencMsg1};
    }

method dsencrtpy(msg:message,sencKey:message,sencMsg:message,advKnw:set<message>) returns (advKnw1:set<message>)
    requires msg in advKnw
    requires sencKey in advKnw
    requires sencMsg !in advKnw
    requires msg == Senc(sencMsg,sencKey)
    requires sencMsg != Var("Nb")
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw1
    ensures sencMsg in advKnw1
    {
        advKnw1:=advKnw+{sencMsg};
    }

method Separate(pairMsg:message,m1:message,m2:message,advKnw:set<message>)returns (advKnw1:set<message>)
    requires pairMsg in advKnw
    requires pairMsg == Pair(m1,m2)
    requires m1 !in advKnw || m2 !in advKnw
    requires m1 != Var("Nb") && m2 != Var("Nb")
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw1
    ensures m1 in advKnw1 && m2 in advKnw1
    {
        advKnw1:=advKnw+{m1,m2};
    }

method Pairing(m1:message,m2:message,advKnw:set<message>) returns (advKnw1:set<message>)
    requires m1 in advKnw
    requires m2 in advKnw
    requires Pair(m1,m2) !in advKnw
    ensures Pair(m1,m2) in advKnw1
{ 
    advKnw1:=advKnw+{Pair(m1,m2)};    
}
method ReceiveMsgFromChannel(c:channel,m1:message,advKnw:set<message>) returns (m:message)//take message from channel
    requires c.Length > 0 
    requires m1!=Nil  
    requires m1 == c[0]
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures m1 == m
    ensures c[0] == Nil
    modifies c
{
    c[0]:=Nil;
    m:=m1;
}
method SendMsgToChannel(c:channel,m:message,advKnw:set<message>)//put the message into channel
    requires c.Length > 0 
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures  c[0] == m
    modifies c
{
    c[0] := m;
}
method AliceSendMsg_1(c:channel,advKnw:set<message>)//Alice sends the first message into channel
    requires c.Length > 0
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures  c[0]!=Nil
    modifies c
{
    var aencMsg:=Pair(Var("Na"),Str("A")); 
    var m :=Aenc(aencMsg,Pk("B")); 
    c[0] := m;
}
method AliceSendMsg_2(c:channel,advKnw:set<message>)//Alice sends the second message into channel
    requires c.Length > 0
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures c[0]!=Nil
    modifies c
{
    var aencMsg:=Var("Nb");
    var m :=Aenc(aencMsg,Pk("B"));
    c[0] :=m;
}
method BobSendMsg_1(c:channel,advKnw:set<message>)//Bob sends the first message into channel
    requires c.Length > 0
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures c[0] != Nil
    modifies c
{
    var aencMsg:=Pair(Var("Na"),Var("Nb"));
    var m :=Aenc(aencMsg,Pk("A"));
    c[0] :=m;
}

 method AliceGetMsg_1(c:array<message>,advKnw:set<message>,flag:bool) returns (m:message)//Alice receives the first message from channel
    requires c.Length > 0 
    requires flag == false
    requires rverify(c[0])
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
  method BobGetMsg_1(c:array<message>,advKnw:set<message>) returns (m:message)//Bob receives the first message from channel
    requires c.Length > 0 
    requires rverify(c[0])
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
  method BobGetMsg_2(c:array<message>,advKnw:set<message>) returns (m:message)//Bob receives the third message from channel
    requires c.Length > 0 
    requires rverify(c[0])
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
method IntruderGetMsg(c:channel,advKnw:set<message>,i:int) returns (advKnw1:set<message>)//intruder intercepts the message in channel and insert it into intruder knowledge databases.
    requires c.Length > 0
    requires iverify(c[0])
    ensures Var("Na") !in advKnw1    // ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0] == Nil
    modifies c
{   
    var aencMsg := destruct(c[0]);
    advKnw1 := advKnw+{aencMsg,c[0]};
    c[0]:=Nil;
}

method IntruderSendMsg(c:channel,m:message,advKnw:set<message>)
    requires c.Length > 0
    requires Var("Nb") !in advKnw
    ensures Var("Nb") !in advKnw
    requires m != Nil
    requires m in advKnw
    ensures c[0]!=Nil
    modifies c
{
    c[0] :=m;
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
 