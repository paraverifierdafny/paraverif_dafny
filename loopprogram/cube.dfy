method cube_0(c:array?<nat>,n:array?<nat>,k:array?<nat>,m:array?<nat>,N:nat) 
requires c!=null && c.Length>0
requires n!=null && n.Length>0
requires m!=null && m.Length>0
requires k!=null && k.Length>0
requires n[0]<N
// requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires forall i,j::0<=i<j<k.Length==>k[i]!=k[j]
requires c[0]==0&&n[0]==0&&k[0]==1&&m[0]==6
ensures n[0]<=N
modifies c
modifies n
modifies k
modifies m
{
    c[0]:=c[0]+k[0];
    k[0]:=k[0]+m[0];
    m[0]:=m[0]+6;
    n[0]:=n[0]+1;
}