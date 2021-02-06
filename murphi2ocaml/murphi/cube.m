type
val_t: 0..30;

var
c : val_t;
n : val_t;
k : val_t;
m : val_t;
N : val_t;



rule "loop"
n < N ==>
begin
c:=c+k;
k:=k+m;
m:=m+6;
n:=n+1;
end;


startstate
c := 0;
n := 0;
k := 1;
m := 6;
N := 20;
end;

invariant "cure"
n<=N & c=n*n*n & k=3*n*n+3*n+1 &m=6*n+6 ;
