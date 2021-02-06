datatype state = I| T| C| E
type client=nat
type boolean=bool




method n_Tryinv__4_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (n[i] == I) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__4_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__4_2(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__4_3(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__4_4(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := T;
}


method n_Critinv__4_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__4_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__4_2(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__4_3(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__4_4(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}


method n_Exitinv__4_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == C)))//3
requires (n[i] == C) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__4_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__4_2(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__4_3(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__4_4(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((x[0] == true) && (n[p__Inv4] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n

{
  n[i] := E;
}


method n_Idleinv__4_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (n[i] == E) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__4_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[i] == E) && (n[p__Inv4] == E)))//3
requires (n[i] == E) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__4_2(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[i] == E) && (n[p__Inv4] == E)))//3
requires (n[i] == E) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__4_3(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[i] == E) && (n[p__Inv4] == E)))//3
requires (n[i] == E) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__4_4(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[i] == E) && (n[p__Inv4] == E)))//3
requires (n[i] == E) //guard condition
ensures   (!((x[0] == true) && (n[p__Inv4] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}


