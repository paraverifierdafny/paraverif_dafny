function method pow(m:int,n:int):int
{
if m==0 then 0 else if m==1 then 1 else if n==0 then 1 else if n == 1 then m else m*pow(m,n-1)
}
method test(){
    var m:=2;
    var n:=6;
    assert pow(m,n/2)==8;
    assert pow(m,n)==64;

}

// method power_binary(m:nat, n: nat) returns (Result: nat)
// //    ensures   Result == pow(m, n)
// {
//    var x, y: int;

//    Result := 1;
//    x := m;
//    y := n;  
//    while (y != 0)
//    invariant  y >= 0
//    invariant  Result * pow(x, y) == pow(m, n)
//    {
//       if (y % 2 == 0)
//       {
//          x := x * x;
//          y := y / 2;
//       }
//       else
//       {
//          Result := Result * x;
//          y := y - 1;
//       }
//    }
// }