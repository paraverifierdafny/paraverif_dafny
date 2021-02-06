function gcd(a:nat,b:nat):nat
{
    
}
method gcd1(result:array?<nat>,x:array?<nat>,a:nat,b:nat)

requires result!=null &&result.Length >0
requires x!=null &&x.Length >0
requires result[0]!=x[0]
requires result[0] > x[0]>0
ensures result[0]>0
modifies result
modifies x
{
    result[0]:=result[0]-x[0];
}

method gcd2(result:array?<nat>,x:array?<nat>,a:nat,b:nat)

requires result!=null &&result.Length >0
requires x!=null &&x.Length >0
requires result[0]!=x[0]
requires x[0]>result[0]>0
ensures result[0]>0
ensures x[0]>result[0]
modifies result
modifies x
{
    result[0]:=x[0]-result[0];
}

method gcd3(result:array?<nat>,x:array?<nat>,a:nat,b:nat)

requires result!=null &&result.Length >0
requires x!=null &&x.Length >0
requires result[0]==x[0] &&result[0]>0
ensures result[0]>0
modifies result
modifies x
{
    result[0]:=result[0];
}