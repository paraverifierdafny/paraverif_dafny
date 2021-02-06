const clientNUMS : 5;
type state : enum{I, T, C, E};

     client: 1..clientNUMS;

var n : array [client] of state;

    x : boolean; 
    
ruleset i : client do
rule "Try" n[i] = I ==> begin
      n[i] := T;end; 

rule "Crit"
      n[i] = T& x = true ==>begin
      n[i] := C; x := false; end;

rule "Exit"
      n[i] = C ==>begin
      n[i] := E;end;
      
 
rule "Idle"
      n[i] = E ==> begin n[i] := I;
      x := true;end;
endruleset;

startstate
begin
 for i: client do
    n[i] := I; 
  endfor;
  x := true;
endstartstate;

ruleset i:client; j: client do
invariant "coherence"
  i != j -> (n[i] = C -> n[j] != C);
endruleset;
