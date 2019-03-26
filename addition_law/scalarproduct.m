forward Multi;

///// multiply ////////



Multi:=function(D1,h0, h1, h2, h3, f0, f1, f2 , k)
Seq:=IntegerToSequence(k-1,2);
p  :=D1;
Di :=D1;
ind:=1;
for i:=1 to #Seq do
	if Seq[i] eq 1 then
	for j:=1 to i-ind do
		Di:=doubling (Di, f0, f1, f2, h0, h1, h2, h3);
	end for;
	if p ne Di then
		p:=addition (p, Di, f0, f1, f2, h0, h1, h2, h3); else p:=doubling (p, f0, f1, f2, h0, h1, h2, h3);
		end if;
	ind:=i;
	end if;
end for;
return p;
end function;

Multi2:=function(D1,h0, h1, h2, h3, f0, f1, f2 , k)
Seq:=IntegerToSequence(k,2);
//#Seq-2;
p:=D1;
i:=#Seq-2;
while (i ge 0) do
	p:=doubling (p, f0, f1, f2, h0, h1, h2, h3);
	if (Seq[i+1] eq 1) then p:=addition (p, D1, f0, f1, f2, h0, h1, h2, h3);
	end if;
	i:=i-1;
end while;
return p;
end function;

NAF:=function(k)
XX:=[];
Seq:=IntegerToSequence(k,2);
Append(~Seq,0);
Append(~Seq,0);
l:=#Seq-1;
s:=0;
ww:=0;
for i:=0 to l-1 do
	t:=Floor((Seq[i+1]+Seq[i+2]+s)/2);
	if ((i eq (l-1)) and (Seq[i+1]+s-2*t eq 0)) then return l-1,ww,XX; end if;
	Append(~XX,Seq[i+1]+s-2*t);
	ww:=ww+AbsoluteValue(Seq[i+1]+s-2*t);
	s:=t;
end for;
return l,ww,XX;
end function;
