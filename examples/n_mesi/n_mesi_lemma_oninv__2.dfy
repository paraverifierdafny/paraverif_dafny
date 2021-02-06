datatype location = M| E| S| I
type client=nat
type boolean=bool




method n_t1inv__2_0(state:array<location>,    
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0




requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]




requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires (!((state[p__Inv2] == E) && (state[p__Inv0] == E)))//3
requires (state[i] == E) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  state[i] := M;
}

method n_t1inv__2_1(state:array<location>,    
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0




requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]




requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (state[i] == E) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  state[i] := M;
}

method n_t1inv__2_2(state:array<location>,    
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0




requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]




requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))//2
requires (state[i] == E) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  state[i] := M;
}


method n_t2inv__2_0(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires (state[p__Inv0] == E)//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_1(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires ((state[p__Inv0] == M) && (!(state[p__Inv0] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_2(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires ((state[p__Inv0] == I) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_3(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
requires ((!(state[p__Inv0] == I)) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_4(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires (state[p__Inv2] == E)//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_5(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires ((state[p__Inv2] == M) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_6(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires ((state[p__Inv2] == I) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_7(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
requires ((!(state[p__Inv2] == I)) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_8(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == E) && (state[p__Inv2] == E))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_9(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == M) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == E))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_10(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == I) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == E))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_11(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(state[p__Inv0] == I)) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == E))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_12(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == E) && (state[p__Inv2] == M) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_13(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == M) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == M) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_14(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == I) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == M) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_15(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(state[p__Inv0] == I)) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == M) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_16(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == E) && (state[p__Inv2] == I) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_17(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == M) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == I) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_18(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == I) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == I) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_19(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(state[p__Inv0] == I)) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (state[p__Inv2] == I) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_20(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == E) && (!(state[p__Inv2] == I)) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_21(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == M) && (!(state[p__Inv0] == E)) && (!(state[p__Inv2] == I)) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_22(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((state[p__Inv0] == I) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (!(state[p__Inv2] == I)) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}

method n_t2inv__2_23(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
requires ((!(state[p__Inv0] == I)) && (!(state[p__Inv0] == M)) && (!(state[p__Inv0] == E)) && (!(state[p__Inv2] == I)) && (!(state[p__Inv2] == M)) && (!(state[p__Inv2] == E)))//branch
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := S;}
else{
      if (state[j] == E) {
        state[j] := S;}
else{
        if (state[j] == M) {
          state[j] := S;}
else{
          if (state[j] == I) {
            state[j] := I;}
else{
            state[j] := S;
          }
        }
      }
    }
  
 j:=j+1;
}
}


method n_t3inv__2_0(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
//1
requires (state[i] == S) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := E;}
else{
      state[j] := I;
    }
  
 j:=j+1;
}
}

method n_t3inv__2_1(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (state[i] == S) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := E;}
else{
      state[j] := I;
    }
  
 j:=j+1;
}
}

method n_t3inv__2_2(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
//1
requires (state[i] == S) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := E;}
else{
      state[j] := I;
    }
  
 j:=j+1;
}
}


method n_t4inv__2_0(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv2
//1
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := E;}
else{
      state[j] := I;
    }
  
 j:=j+1;
}
}

method n_t4inv__2_1(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i==p__Inv0
//1
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := E;}
else{
      state[j] := I;
    }
  
 j:=j+1;
}
}

method n_t4inv__2_2(state:array<location>,     
N0:nat,i:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires state.Length==N0





requires forall i,j::0<=i<state.Length&&0<=j<state.Length==>state[i]!=state[j]





requires 0<=i<N0
requires p__Inv0!=p__Inv2&&p__Inv2<N0&& p__Inv0<N0
requires i!=p__Inv0&&i!=p__Inv2
//1
requires (state[i] == I) //guard condition
ensures   (!((state[p__Inv0] == E) && (state[p__Inv2] == M)))
modifies state

{
  var j:=0;
  while(j<N0)
    decreases N0-j
 {
    if (j == i) {
      state[j] := E;}
else{
      state[j] := I;
    }
  
 j:=j+1;
}
}


