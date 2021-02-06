  datatype state = I| T| C| E
  type client=nat
type boolean=bool




class TopC{
var
x : boolean,
n : array<state>;
constructor (){

}
}

method n_Tryinv__1_0(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
//1
//guard condition
requires   (top.n[i] == I)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := T;
}

method n_Tryinv__1_1(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
//1
//guard condition
requires   (top.n[i] == I)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := T;
}

method n_Tryinv__1_2(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))//2
//guard condition
requires   (top.n[i] == I)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := T;
}


method n_Critinv__1_0(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
requires (!((top.n[p__Inv3] == C) && (top.x == true)))//3
//guard condition
requires   ((top.n[i] == T) && (top.x == true))

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := C;
  top.x := false;
}

method n_Critinv__1_1(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
requires (!((top.n[p__Inv4] == C) && (top.x == true)))//3
//guard condition
requires   ((top.n[i] == T) && (top.x == true))

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := C;
  top.x := false;
}

method n_Critinv__1_2(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))//2
//guard condition
requires   ((top.n[i] == T) && (top.x == true))

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := C;
  top.x := false;
}


method n_Exitinv__1_0(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
//1
//guard condition
requires   (top.n[i] == C)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := E;
}

method n_Exitinv__1_1(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
//1
//guard condition
requires   (top.n[i] == C)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := E;
}

method n_Exitinv__1_2(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))//2
//guard condition
requires   (top.n[i] == C)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := E;
}


method n_Idleinv__1_0(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
//1
//guard condition
requires   (top.n[i] == E)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := I;
  top.x := true;
}

method n_Idleinv__1_1(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
//1
//guard condition
requires   (top.n[i] == E)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := I;
  top.x := true;
}

method n_Idleinv__1_2(top:TopC,i:nat,N0:nat,p__Inv3:nat,p__Inv4:nat)
requires 0<=i<N0

requires N0>0
requires top.n.Length==N0
requires forall i,j::0<=i<top.n.Length&&0<=j<top.n.Length==>top.n[i]!=top.n[j]
ensures top.n==old(top.n)
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))//2
//guard condition
requires   (top.n[i] == E)

ensures   (!((top.n[p__Inv4] == C) && (top.n[p__Inv3] == C)))
modifies top.n
modifies top
modifies top


{
  top.n[i] := I;
  top.x := true;
}


