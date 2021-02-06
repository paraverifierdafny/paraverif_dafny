datatype state = I| T| C| E
type client=nat
type boolean=bool




method n_Tryinv__5_0(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
//1
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__5_1(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
//1
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__5_2(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__5_3(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__5_4(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := T;
}


method n_Critinv__5_0(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__5_1(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__5_2(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__5_3(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__5_4(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}


method n_Exitinv__5_0(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
requires (!((n[p__Inv3] == E) && (n[p__Inv4] == C)))//3
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__5_1(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == C)))//3
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__5_2(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__5_3(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__5_4(n:array<state>,    
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n

{
  n[i] := E;
}


method n_Idleinv__5_0(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv4
//1
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__5_1(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i==p__Inv3
//1
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__5_2(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__5_3(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__5_4(n:array<state>,     x:array<boolean>, 
N0:nat,i:nat,
p__Inv3:nat,p__Inv4:nat)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p__Inv3!=p__Inv4&&p__Inv4<N0&& p__Inv3<N0
requires i!=p__Inv3&&i!=p__Inv4
requires (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))//2
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == E) && (n[p__Inv3] == E)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}


