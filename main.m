

intrinsic main(field::RngIntElt, crt_over::RngIntElt : num_expected := -1) -> RngIntElt
{Input: field = An integer describing which field K to take the CRT over
	crt_over = Use 0 for crt over QQ, 1 for CRT over reflex
 Optional: num_expected = An integer indicating the expected number of curves
	over the finite field FF_p where p is a CRT prime. Knowing this value speeds
	up computation.
 Output: The list of B*H_i where H_i are the class polynomials with respect to K and a
	randomly chosen primitive CM-type}
	SetDebugOnError(true);
	ProfileReset();
	SetProfile(true);
	t := Cputime();

	R1<t> := PolynomialRing(Rationals());
	R2<y> := PolynomialRing(Rationals());

	H_i_mod_p := [];
	primes_for_CRT := [];
	P_prod := 1;

	//crt_over := 0; // 0 is over \QQ, 1 is over reflex
	case field:
	when 1: // Field \QQ(\zeta_9)) Disc = 81
		K_plus<a> := NumberField(y^3  - 3*y - 1);
		B := 3^3;
	
	when 2: // Field 2 K^+ Disc = 49
		K_plus<a> := NumberField(y^3 - y^2 - 2*y + 1);
		B := 2^12;
		//coeff_bound := 38; //for 7 invariants
		coeff_bound := 7;

	when 3: // Field 3 K^+ Disc = 169
		K_plus<a> := NumberField(y^3 - y^2 - 4*y - 1);

	when 4: // Field 4 K^+ Disc = 3844
		K_plus<a> := NumberField(y^3 + y^2 - 10*y - 8);

	when 5: // Field 5 K^+ Disc = 7396
		K_plus<a> := NumberField(y^3 - y^2 - 14*y - 8);
	
	when 6: // Field with Galois group S_3 \times \ZZ/2\ZZ Disc = 148
		K_plus<a> := NumberField(t^3 + t^2 - 3*t - 1);		

	when 7: 
		K_plus<a> := NumberField(t^3 - 4*t - 1);
	end case;

	K<b> := ext<K_plus | t^2 + t + 1>;

	Phi := get_primitive_cm_type(AbsoluteField(K));
	K_reflex, reflex_embd := reflex_field(Phi);

	p := 3; // Skip primes 2 and 3

	while P_prod lt 2*coeff_bound*B do

		p := crt_prime(K, p, Phi: num := 1);

		P_prod *:= p;

		// As p splits completely in the reflex, we can take any prime above p for the CRT step
		if crt_over eq 0 then
			Append(~primes_for_CRT, p);
		end if;
		if crt_over eq 1 then
			Append(~primes_for_CRT, Decomposition(MaximalOrder(K_reflex), p)[1][1]);
		end if;
	
		char_polys, M, p_M, embd := cm_type(K,K_plus, p, Phi);

		K_abs := AbsoluteField(K);

		L_polys := [];

		print "Indices";
		for char_poly in char_polys do
			print Factorization(index_of_lpoly(Reverse(char_poly)));
			Append(~L_polys, Reverse(char_poly));
		end for;
		epsilon := 0.01;
	
		A_p_list := isomorphism_classes(K_abs, L_polys, p, p_M, Phi, embd : num_expected := num_expected);
		Append(~H_i_mod_p, construct_H_i_mod_p(A_p_list, B));

	end while;
	H_i := crt_H_i(H_i_mod_p, primes_for_CRT, B: crt_over := crt_over);	// Assume primes split completely in K_star
	
	SetProfile(false);
	G := ProfileGraph();
	ProfilePrintByTotalTime(G);
    	return H_i;
end intrinsic;

intrinsic crt_over_rationals(H_i_mod_p_list::SeqEnum, primes::SeqEnum, B::RngIntElt) -> RngIntElt
{}
	R<x> := PolynomialRing(Rationals());

	P := 1;
	for prime in primes do
		P *:= prime;
	end for;


	H_i_list := [];
	for i in [1..3] do
		deg_H_i := Degree(H_i_mod_p_list[1][i]);
		H_i := 0;
		for j in [0..(deg_H_i-1)] do
			coeff_j_list := []; // for j-th coeff create list of values mod primes
			for H_i_mod_p_tuple in H_i_mod_p_list do
				Append(~coeff_j_list, Coefficient(H_i_mod_p_tuple[i], j));
			end for;
			lift := CRT(coeff_j_list, primes);

			if lift gt Abs(lift - P) then
				lift := lift - P;
			end if;
			H_i +:= lift*x^j; 

		end for;

		// Degree spits out -1 for zero poly so need cases
		if H_i eq 0 then
			H_i := x;
		else
			H_i := x^(Degree(H_i)+1) + H_i/B;
		end if;

		Append(~H_i_list, H_i);
	end for;

	print "Class polynomials over \CC:", H_i_list;
	return 0;
end intrinsic;

intrinsic crt_H_i(H_i_mod_p::RngUPolElt, primes::SeqEnum, B::RngIntElt: crt_over := 0) -> RngIntElt
{}
	if crt_over eq 0 then
		return crt_over_rationals(H_i_mod_p, primes, B);
	end if;
	if crt_over eq 1 then
		return crt_over_reflex(H_i_mod_p, primes, B);
	end if;
end intrinsic;

intrinsic invariants(C::Crv) -> SeqEnum
{Input : A Picard curve C such that Jac(C) is simple
 Output: The invariants j_1, j_2, j_3 of C as described in [KLS18]}
	coeffs := coefficients_of_picard_curve(C, BaseRing(C));
	R<x> := PolynomialRing(BaseRing(C));
	f := 0;
	for i in [1..#coeffs] do
		f := f + coeffs[i]*x^(i-1);
	end for;

	a_4 := coeffs[1];
	a_3 := coeffs[2];
	a_2 := coeffs[3];

	j_1 := a_2^3/a_3^2;
	j_2 := a_2*a_4/a_3^2;
	j_3 := a_4^3/a_3^4;

	return [j_1, j_2, j_3];
end intrinsic;

intrinsic construct_H_i_mod_p(A_p_list::SeqEnum, B::RngIntElt) -> SeqEnum
{Input: A_p_list = the list of all isomorphism classes of Picard curves/\FF_p whose invariants occur as roots
	of the class polynomials modulo p
	B = A bound on the denominators of the class polys
 Output: The list of B*H_i,p where H_i,p are the class polynomials modulo p}
	num_invs := 3;

	if A_p_list eq [] then
		return [];
	end if;

	R<x> := PolynomialRing(BaseRing(A_p_list[1]));

	H_i_mod_p_list := [];
	
	for i in [1..num_invs] do
		Append(~H_i_mod_p_list, R ! 1);
	end for;
	

	for C in A_p_list do
		invs := invariants(C);
		print invs;
		for i in [1..#invs] do
			H_i_mod_p := H_i_mod_p_list[i];
			H_i_mod_p *:= x - invs[i];
			H_i_mod_p := B*H_i_mod_p;
			Remove(~H_i_mod_p_list, i);
			Insert(~H_i_mod_p_list, i,  H_i_mod_p);
		end for;		
	end for;

	// Convert to integer coefficients for simplicity
	R2<x> := PolynomialRing(IntegerRing());
	H_i_mod_p_list_int := [];
	for poly in H_i_mod_p_list do
		Append(~H_i_mod_p_list_int, R2 ! poly);
	end for;

	return H_i_mod_p_list_int;
end intrinsic;

intrinsic crt_over_reflex(H_i_mod_p_list::SeqEnum, primes::SeqEnum, B::RngInt) -> RngIntElt
{}
	O := Order(primes[1]);
	R<x> := PolynomialRing(NumberField(O));

	P := ideal<O | 1>;
	for prime in primes do
		P *:= prime;
	end for;
	L, embd := Lattice(P);
	L_O, embd_O := Lattice(O);
	basis := Basis(P);
	basis_O := Basis(O);

	H_i_list := [];
	for i in [1..7] do
		deg_H_i := Degree(H_i_mod_p_list[1][i]);
		H_i := 0;
		for j in [0..(deg_H_i-1)] do
			coeff_j_list := []; // for j-th coeff create list of values mod primes
			for H_i_mod_p_tuple in H_i_mod_p_list do
				Append(~coeff_j_list, O ! IntegerRing() ! Coefficient(H_i_mod_p_tuple[i], j));
			end for;
			lift := CRT(coeff_j_list, primes);
			lift_embd := embd_O(lift);
			short_vec := ShortestVectors(L)[1];
			v := ClosestVectors(L, lift_embd)[1];
			coords := Coordinates(v);
			c_x := 0;

			for k in [1..#coords] do
				c_x +:= basis[k]*coords[k];
			end for;

			H_i +:= (O ! lift - c_x)*x^j; 

		end for;

		// Degree spits out -1 for zero poly so need cases
		if H_i eq 0 then
			H_i := x;
		else
			H_i := x^(Degree(H_i)+1) + H_i/B;
		end if;

		Append(~H_i_list, H_i);
	end for;

	print "Class polynomials over \CC:", H_i_list;


	return 0;
end intrinsic;

intrinsic index_of_lpoly(lpoly::RngUPolElt) -> RngIntElt
{Input: lpoly = The LPolynomial of a simple, ordinary abelian variety A
 Ouput: The index [\cO_K : \ZZ[\pi,\pi_bar]] where \cO_K is generated by
	a root of the characteristic polynomial of frob of A and pi is a root of
	the characteristic poly}

	char_poly := Reverse(lpoly);
	K<gen> := NumberField(char_poly);
	O := MaximalOrder(K);
	E := sub<O | gen, ComplexConjugate(gen)>;

	return Index(O, E);
end intrinsic;


intrinsic in_isogeny_class(C, L_polys::SeqEnum : num_points := 1) -> BoolElt
{Input : C = A Picard Curve
	L_polys = A list of all LPolynomials for all simple, ordinary abelian varieties A with
		End(A) \cong \cO_K, the maximal order in a sextic CM-field
Optional: num_points = A list of the number of points for all Picard curves with
}
	for i in [1..num_points] do
		test := false;
		P := random_point_jacobian(C, CoefficientRing(Parent(DefiningPolynomial(C))));
		for l_poly in L_polys do
			m := IntegerRing() ! Evaluate(Reverse(l_poly), 1);
			if is_zero_jac_multi(P,C,m) eq true then
				test := true;
				break;
			end if;
		end for;
		if test eq false then
			return false;
		end if;
	end for;
	try
		return LPolynomial(C) in L_polys;
	catch e
		print "Error with curve", C;
		print e;

		return false;
	end try;
end intrinsic;


intrinsic isomorphism_classes(K_abs::FldNum, L_polys::SeqEnum, p::RngIntElt,  p_M::RngOrdIdl, Phi::SeqEnum, embd::Map : num_expected := -1) -> SeqEnum
{}

	k := FiniteField(p);
	A<x,y> := AffineSpace(k,2);
	A_p_list := [];
	K := Domain(embd);

	M := NumberField(Order(p_M));
	G := Automorphisms(M);
	print "Enumerating Picard curves from invariants";
	print "Case 1 type Picard curves of Koike-Weng";
	i := 0; 
	for j_1 in k do
		for j_2 in k do
			if j_1 ne 0 then //j_1 = 0 implies g_3 = 0
				f := x^4 + j_1*x^2 + j_1^2*x + j_1^2*j_2;
				C := Curve(A, [y^3 - f]);
				if i mod 1000 eq 0 then
					print "Curve #: ", i;
				end if;
				i +:= 1;

				if in_isogeny_class(C, L_polys) then
					print C;
					if satisfy_norm_cond(C, p_M, K, Phi, embd) then
						if is_endo_ring(C, Reverse(LPolynomial(C)), k) eq true then
							Append(~A_p_list, C);
							if #A_p_list eq num_expected then
								return A_p_list;
							end if;
						end if;
					end if;
				end if;
			end if;
		end for;
	end for;


	print "Case 2";
	// Case 2: If g_2 \ne 0, g_3 = 0
	for j_2 in k do
		b := 2;
		f := x^4 + x^2 + j_2;
		C := Curve(A, [y^3 - f]);
		if in_isogeny_class(C, L_polys) then
			if satisfy_norm_cond(C, p_M, K, Phi, embd) then
				if is_endo_ring(C, Reverse(LPolynomial(C)), k) eq true then
					Append(~A_p_list, C);
					if #A_p_list eq num_expected then
						return A_p_list;
					end if;
				end if;
			end if;
		end if;
	end for;

	print "Case 3";
	// Case 3: If g_2 = 0, g_3*g_4 \ne 0
	for j in k do
		if j ne 0 then
			f := x^4 + (1/j)*x + (1/j);
			C := Curve(A, [y^3 - f]);
			if in_isogeny_class(C, L_polys) then
				if satisfy_norm_cond(C, p_M, K, Phi, embd) then
					if is_endo_ring(C, Reverse(LPolynomial(C)), k) eq true then
						Append(~A_p_list, C);
						if #A_p_list eq num_expected then
							return A_p_list;
						end if;
					end if;
				end if;
			end if;
		end if;
	end for;

	print "Case 4";
	f := x^4 + x;
	C := Curve(A, [y^3 - f]);
	if in_isogeny_class(C, L_polys) then
		if satisfy_norm_cond(C, p_M, K, Phi, embd) then
			if is_endo_ring(C, Reverse(LPolynomial(C)), k) eq true then
				Append(~A_p_list, C);
				if #A_p_list eq num_expected then
					return A_p_list;
				end if;
			end if;
		end if;
	end if;

	print "Case 5";

	// Case 5: If g_4 = 0, g_3 = 0.
	f := x^4 + 1;
	C := Curve(A, [y^3 - f]);
	if in_isogeny_class(C, L_polys) then
		if satisfy_norm_cond(C, p_M, K, Phi, embd) then
			if is_endo_ring(C, Reverse(LPolynomial(C)), k) then
				Append(~A_p_list, C);
				if #A_p_list eq num_expected then
					return A_p_list;
				end if;
			end if;
		end if; 
	end if;

	return A_p_list;
end intrinsic;


 

intrinsic satisfy_norm_cond(C::Crv, p_M::RngOrdIdl, K::FldNum, Phi::SeqEnum, embd::Map) -> BoolElt
{Input: C = A Picard curve over a finite field
	p_M = A prime in the field M
	K = A number field contained in M
	Phi = A CM-type on K
	embd = An embedding of K into M
 Output: True if frob of C satisfies the conditions of Prop 2.4 of [AE19], false otherwise }
	char_poly := Reverse(LPolynomial(C));
	R, h := ChangeRing(Parent(char_poly), K);
	roots := Roots(h(char_poly));

	M := Codomain(embd);
	Phi_gen := [t(K.1) : t in Phi];
	for sig in Automorphisms(M) do
		Phi_M_inv := [sig^(-1)*g^(-1) : g in Automorphisms(M) | g(embd(K.1)) in Phi_gen];

		// construct pi_ideal in terms of
		O := MaximalOrder(M);
		pi_ideal := ideal<O|1>;
		P_gens := Generators(p_M);

		for aut in Phi_M_inv do
			P_gens_aut := [];
			for gen in P_gens do
				Append(~P_gens_aut, aut(gen));
			end for;
			pi_ideal *:= ideal<O|P_gens_aut>;
		end for;

		for pi in roots do
			if ideal<O|embd(pi[1])> eq pi_ideal then
				return true;
			end if;
		end for;
	end for;

	return false;
		
end intrinsic;


	 


intrinsic cm_type(K::FldNum, K_plus::FldNum, p::RngIntElt, Phi::SeqEnum) -> SeqEnum, FldNum, RngOrdIdl, Map
{}

	
	M := Codomain(Universe(Phi));
	O := MaximalOrder(M);

	primes_above := Decomposition(MaximalOrder(M), p);
	P := primes_above[1][1];
	// We wish to think of K as a subfield of M. Thus, we fix an embd of K into M for
	// the rest of the intrinsic. This does not matter because we are working with an
	// arbitrary primitive cm type. In particular, changing the embedding will just change
	// the primitive CM type we are dealing with.
	embd := Phi[1]; 
	
	print "Num Phi: ", #Phi;
	Phi_gen := [t(AbsoluteField(K).1) : t in Phi];

	pi_ideals := [];
	for sigma in Automorphisms(M) do
		Phi_M := [g*sigma : g in Automorphisms(M) | g(embd(AbsoluteField(K).1)) in Phi_gen];
		print "Num Phi_M: ", #Phi_M;
		Phi_M_inv := {g^(-1) : g in Phi_M};
		print #Phi_M_inv;
		pi_ideal := ideal<O|1>;
		P_gens := Generators(P);
		for aut in Phi_M_inv do
			P_gens_aut := [];
			for gen in P_gens do
				Append(~P_gens_aut, aut(gen));
			end for;
			pi_ideal *:= ideal<O|P_gens_aut>;
		end for;
		Include(~pi_ideals, pi_ideal);
	end for;
	print "#pi_ideals", #pi_ideals;
	_, frobs := NormEquation(MaximalOrder(K), MaximalOrder(K_plus) ! p);

	unit_group, rho := UnitGroup(AbsoluteField(K));
	zeta := AbsoluteField(K) ! rho(unit_group.1);
	order_zeta := order_of_element(zeta);
	frob_list := {};

	for frob in frobs do

		if (embd(frob))*O in pi_ideals or ComplexConjugate(embd(frob))*O in pi_ideals then
			for i in [1..order_zeta] do
				if IsIrreducible(CharacteristicPolynomial(AbsoluteField(K) ! frob*zeta^i)) eq false then
					print "Not Irreducible";
					continue;
				end if;
				Include(~frob_list, CharacteristicPolynomial(AbsoluteField(K) ! frob*zeta^i));
				Include(~frob_list, CharacteristicPolynomial(AbsoluteField(K) ! -frob*zeta^i));
			end for;
		end if;
	end for;

	return frob_list, M, P, embd;
end intrinsic;

intrinsic order_of_element(alpha::FldNumElt) ->RngIntElt
{}
	i := 1;
	while true do
		if alpha^i eq 1 then
			return i;
		end if;
		i +:= 1;
	end while;
end intrinsic;

// Change splitting condition to split in reflex
intrinsic crt_prime(K::FldNum, p::RngIntElt, Phi::SeqEnum : num := 1) ->RngIntElt
{}
	K_star := reflex_field(Phi);
	K_abs := AbsoluteField(K);
	O := MaximalOrder(K_abs);
	O_K_star := MaximalOrder(K_star);
	for i in [1..num] do
		p := NextPrime(p);
		while true do
			if IsTotallySplit(p, O) and splits_into_principal_ideals(O_K_star,p) then
				break;
			end if;
			p := NextPrime(p);
		end while;
	end for;
	return p;
end intrinsic;

intrinsic splits_into_principal_ideals(O::RngOrd, p::RngIntElt) -> BoolElt
{}

	if IsTotallySplit(p, O) eq false then
		return false;
	end if;

	for P in Decomposition(O, p) do
		fP := P[1];
		if IsPrincipal(fP) eq false then
			return false;
		end if;
	end for;
	
	return true;
end intrinsic;


