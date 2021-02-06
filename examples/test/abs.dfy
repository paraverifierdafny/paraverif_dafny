method sum(x:int,a:array?<int>) returns (result:int)
requires a!=null
requires a.Length>0
{
    var i:=0;
    while(0<=i<a.Length)
        invariant 0<=i<=a.Length
    {
        result:=result+a[i];
        i:=i+1;
    }
}