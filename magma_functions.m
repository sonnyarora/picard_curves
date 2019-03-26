// From avisogenies
GetFullTorsionExtension := function(l,frob)
  kk:=1;
  P<x>:=PolynomialRing(ResidueClassRing(l));
  for f in Factorization(P!frob) do
    Q<y>:=quo<P|f[1]>;
    k:=#Q-1;
    for p in Factorization(k) do for i in [1..p[2]] do
      if y^(k div p[1]) eq 1 then k div:=p[1]; end if;
    end for; end for;
    if f[2] gt 1 then
      Q<y>:=quo<P|f[1]^f[2]>;
      k1:=k; y1:=y^k1; yy:=y1;
      while yy ne 1 do k+:=k1; yy*:=y1; if k gt #Q then return 0; end if; end while;
    end if;
    kk:=LCM(kk,k);
  end for;
  return kk;
end function;

element_in_terms_of_frob := function(alpha, gen, i)
	CC := ComplexField();
	pis := Conjugates(gen);
	alphas := Conjugates(alpha);


	coeffs := IntegerRelation([CC ! 1, pis[1], pis[1]^2, pis[1]^3, pis[1]^4, pis[1]^5, -alphas[1]]);
	return coeffs[i];
end function;



num_points_on_jac := function(char_poly, m);
	K<gen> := NumberField(char_poly);
	poly := CharacteristicPolynomial(gen^m);

	return IntegerRing() ! Evaluate(poly, 1);
end function;


deg_of_field_of_defn_of_n_tors := function(char_poly, n)

	K<pi> := NumberField(char_poly);
	O := MaximalOrder(K);	
	I := O*n;
	mod_I := quo<O | I>;

	k := 1;
	while true do
		if IsZero(mod_I ! (pi^k - 1)) then
			return k;
		end if;
		k +:= 1;
	end while;

	return 0;
	
end function;


size_of_prime_power := function(num, l)
	s := 0;
	while true do
		if num mod l^(s+1) ne 0 then
			return s;
		end if;
		s := s + 1;
	end while;
end function;




