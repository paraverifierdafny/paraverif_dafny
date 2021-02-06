type
	val_t:0..1000;
var
	x : val_t;
	y : val_t;
	r : val_t;
	temp: val_t;

Procedure gcd(Var x,y,r: val_t);
begin
	while r!= 0 do
		x := y;
		y := r;
		r := x % y;
	end;
	put(y);
end;

rule r > 0 ==> begin gcd(x,y,r); end;
rule x<y ==> begin temp :=y; y := x; x := temp; end;
	
startstate  -- 测试用例，x是被除数，y是除数，r是余数。特地设置成x<y。
	x := 12;  
	y := 16;
	r := x%y;
end;


-- 不变量／安全性质
invariant r > 0;