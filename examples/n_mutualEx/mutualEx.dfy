datatype state = I| T| C| E
type client=nat
type boolean=bool

method n_Try_1(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires i==p__Inv1
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires  (n[i] == I) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
{
  n[i] := T;
}
method n_Try_2(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires i==p__Inv2
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires  (n[i] == I) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
{
  n[i] := T;
}
method n_Try_3(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires !(i==p__Inv2 && i==p__Inv1)
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires  (n[i] == I) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
{
  n[i] := T;
}

method n_Crit__1(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires i==p__Inv1
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}


method n_Crit__2(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
 requires i==p__Inv2
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := C;
  x[0] := false;
}

method n_Crit__3(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires !(i==p__Inv2 && i==p__Inv1)
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := C;
  x[0] := false;
}

method n_Exit__1(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires i==p__Inv1
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := E;
}

method n_Exit__2(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires i==p__Inv2
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := E;
}

method n_Exit__3(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires !(i==p__Inv2 && i == p__Inv1)
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := E;
}

method n_Idle__1(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires i==p__Inv1
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := I;
  x[0] := true;
}

method n_Idle__2(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires i==p__Inv2
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := I;
  x[0] := true;
}

method n_Idle__3(n:array<state>, x:array<boolean>,N0:nat,i:nat,p__Inv1:nat,p__Inv2:nat)
requires N0>0
requires n.Length==N0
requires x.Length==N0
requires 0<=i<N0
requires p__Inv1!=p__Inv2&&p__Inv2<N0&& p__Inv1<N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires !(i==p__Inv1 && i==p__Inv2)
requires   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == C)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
requires   (!((x[0] == true) && (n[p__Inv2] == E)))
requires   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv2] == C) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == C)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == C)))
ensures   (!((x[0] == true) && (n[p__Inv2] == E)))
ensures   (!((n[p__Inv2] == E) && (n[p__Inv1] == E)))
modifies n
modifies x
{
  n[i] := I;
  x[0] := true;
}