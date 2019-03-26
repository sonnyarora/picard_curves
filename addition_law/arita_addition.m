intrinsic jCompose(I::RngMPol, J::RngMPol, P::RngMPol) -> FldNum
{}
	K := I*J+P;
	Groebner(K);
	return K;
end intrinsic;

intrinsic MinimumNonZeroFnc(I::RngMPol, P::RngMPol) -> RngMPolElt
{}
	i := #Basis(I);
	while i gt 0 do
		f := Basis(I)[i];
		if NormalForm(f, P) ne 0 then
			return f;
		end if;
		i := i - 1;
	end while;
	return 0; // error
end intrinsic;

intrinsic jReduce(I::RngMPol, P::RngMPol, R::RngMPol) -> RngMPol, RngMPolElt
{}
	//print I;
	//print P;
	f := MinimumNonZeroFnc(I, P);
	//R := Parent(P);
	//print Type(Ideal(f));
	J := ideal<R | f> + P;
	Groebner(J);
	J := IdealQuotient(J,I) + P;
	Groebner(J);
	return J,f;
end intrinsic;

intrinsic jInverse(I::RngMPol, P::RngMPol, R::RngMPol) -> FldNum, RngMPolElt
{}
	K, f := jReduce(I, P, R);
	return K, f; 
end intrinsic;

intrinsic jSum(I::RngMPol, J::RngMPol, P::RngMPol, R::RngMPol) -> FldNum, SeqEnum
{}
	K := jCompose(I,J, P);
	K,f := jReduce(K, P, R);
	K,g := jReduce(K,P, R);
	return K, [f, g]; //f := Numerator, g := Denominator
end intrinsic;

intrinsic jPower(n::RngIntElt, I::RngMPol,P::RngMPol,R::RngMPol) -> RngMPol
{}
	r := ideal<R | 1>; // zero element
	e := I;
	i := n;
	while i gt 0 do
		if (i mod 2) eq 1 then
			r := jSum(r, e, P,R);
			i := (i-1) div 2;
		else
			i := i div 2;
		end if;
		if i gt 0 then
			e := jSum(e, e, P,R);
		end if;
	end while;
	return r;
end intrinsic;

intrinsic jPower_with_function(D::RngMPol, m::RngIntElt, C::CrvPln : add_alg := 1, add_chain := 2) -> SeqEnum
{}
        g_poly_ring := Parent(Generators(D)[1]);
	g_x := Name(g_poly_ring,1);
	g_y := Name(g_poly_ring,2);
	ff_q := PrimeRing(g_poly_ring);
	f_coeffs := coefficients_of_picard_curve(C, ff_q);
	f := 0;
	for i in [1..#f_coeffs] do
		f +:= f_coeffs[i]*g_x^(i-1);
	end for;
	f := g_y^3 - f;
	P := ideal< g_poly_ring | f >;
        I := ideal<g_poly_ring | 1>; // zero element
	K := D^m + P;
	Groebner(K);
        K,f := jReduce(K, P, g_poly_ring);
        coeff,g := jReduce(K, P, g_poly_ring);
	return [[f,g]];

end intrinsic;
