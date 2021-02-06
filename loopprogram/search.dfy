method max(a:array<int>) returns (r:int)
requires a!=null && a.Length>0
{
    var i:=0;
    r:=a[i];
    while i<a.Length
        decreases a.Length-i
        invariant 0<=i<=a.Length
    {
        if r<a[i]
        {
            r:=a[i];
        }
        i:=i+1;
    }
} 
function max(a:int,b:int):nat
{
    if a>b then a else b
}
function maxarray(a:array)
{
    maxarray(a)=max(a)
}

method max_one_way(a:array<int>,t:array<int>,t1:array<int>)returns (r:int)
requires a!=null && a.Length>0
requires t!=null && t.Length>0
requires t1!=null && t1.Length>0
requires forall i,j::0<=i<t1.Length&&0<=j<t1.Length==>t1[i]!=t1[j]
requires forall i,j::0<=i<t.Length&&0<=j<t.Length==>t[i]!=t[j]
requires forall i,j::0<=i<a.Length&&0<=j<a.Length==>a[i]!=a[j]
requires t[0]<a.Length
ensures r == t1[0]
{
    t1[0]:=max(a);
    t[0]:=a[0];
    if r<a[t[0]]
    {
        r:=a[t[0]];
    }
    t[0]:=t[0]+1;
 }