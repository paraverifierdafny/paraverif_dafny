method test5(x:array<int>,y:array<int>,n:int)
requires 0<=n
requires 0< x.Length
requires 0< y.Length  
requires x[0]==y[0]; 
requires (x[0]>=0 ==> y[0]>=0)
requires  (y[0]>= 0 ==> x[0]>= 0)
requires  (x[0]+y[0]==0 || x[0]+y[0]>0);
modifies y;  
modifies x; 
ensures  (x[0]==y[0]); 
ensures (x[0]>0 ==> y[0]>0)
ensures (y[0] > 0 ==> x[0] > 0)
ensures  (x[0]+y[0]==0 || x[0]+y[0]>0)     
{     if (x[0]>0)
    {x[0]:=x[0]- 1; 
     y[0]:=y[0]- 1;
     }
} 