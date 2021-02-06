datatype locationType = M| OSTATUS| E| S| I
type client=nat
type boolean=bool




method n_rule_t1inv__3_0(a:array<locationType>,    
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0




requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]




requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
//1
requires (a[i] == E) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  a[i] := M;
}

method n_rule_t1inv__3_1(a:array<locationType>,    
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0




requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]




requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (a[i] == E) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  a[i] := M;
}

method n_rule_t1inv__3_2(a:array<locationType>,    
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0




requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]




requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))//2
requires (a[i] == E) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  a[i] := M;
}


method n_rule_t2inv__3_0(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires (a[p__Inv0] == E)//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_1(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires ((a[p__Inv0] == M) && (!(a[p__Inv0] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_2(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires ((!(a[p__Inv0] == M)) && (!(a[p__Inv0] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_3(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires (a[p__Inv2] == E)//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_4(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires ((a[p__Inv2] == M) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_5(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires ((!(a[p__Inv2] == M)) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_6(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((a[p__Inv0] == E) && (a[p__Inv2] == E))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_7(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((a[p__Inv0] == M) && (!(a[p__Inv0] == E)) && (a[p__Inv2] == E))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_8(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(a[p__Inv0] == M)) && (!(a[p__Inv0] == E)) && (a[p__Inv2] == E))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_9(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((a[p__Inv0] == E) && (a[p__Inv2] == M) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_10(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((a[p__Inv0] == M) && (!(a[p__Inv0] == E)) && (a[p__Inv2] == M) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_11(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(a[p__Inv0] == M)) && (!(a[p__Inv0] == E)) && (a[p__Inv2] == M) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_12(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((a[p__Inv0] == E) && (!(a[p__Inv2] == M)) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_13(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((a[p__Inv0] == M) && (!(a[p__Inv0] == E)) && (!(a[p__Inv2] == M)) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}

method n_rule_t2inv__3_14(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(a[p__Inv0] == M)) && (!(a[p__Inv0] == E)) && (!(a[p__Inv2] == M)) && (!(a[p__Inv2] == E)))//branch
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := S;}
else{
      if (a[j] == E) {
        a[j] := S;}
else{
        if (a[j] == M) {
          a[j] := OSTATUS;}
else{
          a[j] := a[j];
        }
      }
    }
  
 j:=j+1;
}
}


method n_rul_t3inv__3_0(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
//1
requires (a[i] == S) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}

method n_rul_t3inv__3_1(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (a[i] == S) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}

method n_rul_t3inv__3_2(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
//1
requires (a[i] == S) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}


method n_rul_t4inv__3_0(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
//1
requires (a[i] == OSTATUS) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}

method n_rul_t4inv__3_1(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (a[i] == OSTATUS) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}

method n_rul_t4inv__3_2(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
//1
requires (a[i] == OSTATUS) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}


method n_rul_t5inv__3_0(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
//1
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}

method n_rul_t5inv__3_1(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}

method n_rul_t5inv__3_2(a:array<locationType>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires a.Length==N0





requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
//1
requires (a[i] == I) //guard condition
ensures   (!((a[p__Inv0] == E) && (a[p__Inv2] == E)))
modifies a

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      a[j] := E;}
else{
      a[j] := I;
    }
  
 j:=j+1;
}
}


