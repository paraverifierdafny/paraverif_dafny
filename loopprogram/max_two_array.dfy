function max(a: array？<int>,  left:int, right: int): (int)
// axiom (forall a: array T,  i          : int  ::  max(a, i, i) == a[i]);
// axiom (forall a: array T,  left, right: int  ::  (exists i: int  ::  left <  i && i <= right && a[left] <: a[i])  
//  ==>  max(a, left, right) == max(a, left + 1, right));
// axiom (forall a: array T,  left, right: int  ::  (exists i: int  ::  left <= i && i <  right && a[right] <: a[i])
//   ==>  max(a, left, right) == max(a, left, right - 1));
requires a!=null
requires a.Length>0
requires left>=0&&left<a.Length
requires right>=0&&right<a.Length
requires right >=left
decreases right-left
reads a
{
    if exists i:: left<=i&&i<right&&a[i]>=a[left] then max(a,left+1,right) else if exists i:: left<i<=right&&a[right]<=a[i] then  max(a,left,right-1) else a[left]
}
method max_two_way (a: array?<int>,  n: int) returns (Result: int)
   requires  n > 0;
   requires a!=null && a.Length>0
   requires n>=0 && n<a.Length
   ensures   Result == max(a, 0, n-1);
{
   var i, j: int;

   i := 0;  j := n-1;
   while (i < j)
      invariant  0 <= i && i <= j && j <= n-1;
      invariant  max(a,0, n-1) == max(a, i, j);
   {
      if (a[i] > a[j])
      {
         j := j - 1;
      }
      else
      {
         i := i + 1;
      }
   }
   Result := a[i];
}
