function f(k:int):int  
    requires k>=1;
{
    (exp(2,3*k)-exp(3,k))/5
}

function exp(x:int,e:int):int
    requires e>=0
{
    if e == 0 then 1 else x * exp(x,e-1)
}

method compute5f(k:int) returns (r:int)
    requires k>=1
    ensures r==5*f(k)
{
    var i,t1,t2:=0,1,1;
    while i<k
        invariant 0<=i<=k;
        invariant t1==exp(2,3*i);
        invariant t2==exp(3,i);
        {
            // assume 8*t1==exp(2,3*(i+1));
            expPlus3_Lemma(2,3*i);
            i,t1,t2:=i+1,8*t1,3*t2;
            // assume t1==exp(2,3*i);
            // assert t1==exp(2,3*i);a
        }
    r:=t1-t2;
    DivBy5_Lemma(k);
}

lemma expPlus3_Lemma(x:int,e:int)
    requires e>=0;
    ensures x*x*x*exp(x,e)==exp(x,e+3);
    {
        assert x*x*x*exp(x,e)==x*x*exp(x,e+1)==x*exp(x,e+2)==exp(x,e+3);
    }
lemma DivBy5_Lemma(k:int)
    requires k>=1
    ensures (exp(2,3*k)-exp(3,k))%5==0
    {
        // if k==1 {

        // }else{
        //     calc{
        //         (exp(2,3*k)-exp(3,k)) % 5;
        //         ==
        //         (exp(2,3*(k-1)+3)-exp(3,(k-1)+1))%5;
        //         =={
        //             expPlus3_Lemma(2,3*(k-1));
        //         }
        //         (exp(2,3*(k-1))*8-exp(3,(k-1))*3)%5;
        //         ==
        //         (3 *(exp(2,3*(k-1))-exp(3,k-1))+5*exp(2,3*(k-1)))%5;
        //         ==
        //         {
        //             DivBy5_Lemma(k-1);
        //         }
        //         0;
        //     }
        // }
        if k>1 {
            expPlus3_Lemma(2,3*(k-1));
            DivBy5_Lemma(k-1);
        }
    }