

intrinsic deg_of_field_of_defn_of_n_tors(char_poly::RngUPolElt, n::RngIntElt) -> RngIntElt
{}
	
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
	
end intrinsic;

intrinsic element_to_coeffs(alpha::FldOrdElt, gen::FldNumElt) -> SeqEnum
{}
	K := Parent(gen);
	O := MaximalOrder(K);
	lcm := 1;
	coeffs := [];
	for a in Eltseq(K ! alpha) do
		lcm := LCM(lcm, Denominator(a));
	end for;
	for a in Eltseq(K ! alpha) do
		Append(~coeffs, Numerator(a)*(IntegerRing() ! (lcm/Denominator(a))));
	end for;
	Append(~coeffs, lcm);
	return coeffs;
end intrinsic;

intrinsic get_kummer_map(pi::FldNumElt, k::RngIntElt, n::RngIntElt) -> SeqEnum
{}
	return Eltseq((pi^k -1)/n);
end intrinsic;


// !!! MIGHT NEED ADJUSTMENTS TO DEAL WITH EXTENSIONS OF A PRIME FIELD !!!
intrinsic is_endo_ring(C::Crv, char_poly::RngUPolElt, ff_p::FldFin : addition_law := 1) -> BoolElt
{Input: C = A Picard curve over a prime field ff_p
	char_poly = the characteristic polynomial of C
	ff_p = Field of definition for C
 Optional: addition_law = The addition algorithm used on Jac(C). The default 1 is Arita's algorithm.
		0 is the Flon-Oyono algorithm. However, 0 has not been suitably tested.
 Output: True if End(C) isomorphic to O_K where K is a field obtained by adjoining a root of char_poly,
	false otherwise.}
 
	K2<gen> := NumberField(char_poly);
	R<x> := PolynomialRing(K2);

	try
		zeta := K2 ! Roots(x^2 + x + 1)[1][1];
	catch e
		error "\zeta_3 not in CM field";
	end try;

	O := MaximalOrder(K2);
	E := sub<O | gen, ComplexConjugate(gen), zeta>;
	basis := Basis(O);
	index_factors := Factorization(Index(O,E));
	print "Index of \cO_K in \ZZ[\pi,\pi_bar, \zeta_3]: ", index_factors;

	for fact in index_factors do
		l := fact[1];

		d := max_l_valuation(basis, gen, l);

		if d eq 0 then
			continue;
		end if;

		f := DefiningPolynomial(C);
		p := Characteristic(ff_p);
	
		k := GetFullTorsionExtension(l, char_poly);
		print "d: ", d;
		for i in [1..d] do
			print "l: ", l;
			print "i: ", i;
			if check_endomorphisms(C, [l, i, k], ff_p, char_poly, gen, basis: add_alg := addition_law) eq false then
				return false;
			end if;

			// Add endos to ring
			for alpha in basis do
				coeffs := element_to_coeffs(alpha, gen);
				n := coeffs[#coeffs];
				if size_of_prime_power(n, l) ge i then				
					E := E + sub<O | (IntegerRing() ! (n/l^i))*alpha>;
					if E eq O then
						print "Has Full endo ring";
						return true;
					end if;
				end if;
			end for;

		end for;

		print l, fact[2];
	end for;

	print "Has Full endo ring";

	return true;

end intrinsic;

intrinsic zeta3_ideal(D::RngMPol, C::Crv) -> RngMPol
{}
	g_poly_ring := Parent(Generators(D)[1]);
	print Parent(D);
	ff_q_prime := BaseRing(Parent(Generators(D)[1]));
	g_x := Name(g_poly_ring,1);
	g_y := Name(g_poly_ring,2);	
        pts := ideal_to_divisor(D,C);
        l := Parent(pts[1][1]);
        R<x,y> := PolynomialRing(l,2);
        x_list := [];
        y_polys := [];
	temp_ring<t> := PolynomialRing(ff_q_prime);
	zeta := Roots(t^2+t+1)[1][1];
	for i in [1..#pts] do
		pts[i][2] := pts[i][2]*zeta;
	end for;
        for pt in pts do
                x0 := pt[1];
                y0 := 1;
                for pt1 in pts do
                        if pt1[1] eq x0 then
                                y0 := y0*(y - pt1[2]);
                        end if;
                end for;
                if x0 in x_list eq false then
                        Append (~x_list, x0);
                end if;
                Append(~y_polys, y0);
        end for;

	u := 1;
        w := 1;
        for pt in pts do
                u := u*(x-pt[1]);
        end for;
        if #x_list eq 1 then
                if #pts eq 1 then
                        w := y_polys[1];
                end if;
                if #pts eq 2 or #pts eq 3 then
                        w := y_polys[1];
                end if;
        end if;
        if #x_list eq 2 then
                if #pts eq 2 then
                        w := y - Interpolation(x_list, [R ! pts[1][2], pts[2][2]], 1);
                end if;
                if #pts eq 3 then
                        w := (x - x_list[2])/(x_list[1] - x_list[2])*y_polys[1] + (x - x_list[1])/(x_list[2] - x_list[1])*y_polys[2];
                end if;
        end if;
        if #x_list eq 3 then
                w := y - Interpolation(x_list, [R ! pts[1][2], pts[2][2], pts[3][2]], 1);
        end if;

        return ideal<g_poly_ring| g_poly_ring ! u, g_poly_ring ! w>;

end intrinsic;

intrinsic frob_ideal(Q::RngMPol,q::RngIntElt) -> RngMPol
{}
	gens := Generators(Q);
	g_poly_ring := Parent(gens[1]);
	temp_gens := [];
	for gen in gens do
		temp_gen := 0;
		for i in [1..#Coefficients(gen)] do
			temp_gen +:= Coefficients(gen)[i]^q*Monomials(gen)[i]; 
		end for;
		Append(~temp_gens,temp_gen);
	end for;
	return ideal<g_poly_ring | temp_gens>;
end intrinsic;

intrinsic frob(Q::SeqEnum, q::RngIntElt) -> SeqEnum
{}
	x := Name(Q[1], 1);
	for k in [1..2] do
		p := Q[k];
		temp := 0;
		for i in [1..Degree(p)+1] do
			temp +:= Coefficient(p,i-1)^q*x^(i-1);
		end for;
		Q[k] := temp;
	end for;

	return Q;
end intrinsic;


intrinsic apply_kummer_map(D::RngMPol, kummer::SeqEnum, C::Crv) -> RngMPol
{}
	ff_q := BaseRing(Parent(Generators(D)[1]));
	p := Characteristic(ff_q);
	frob_list := [D];
	g := 3;
	for i in [1..(2*g-1)] do
		Include(~frob_list, frob_ideal(D, p^i));
	end for;
	return linear_combo(frob_list, kummer, C, ff_q);
end intrinsic;


// Characteristic polynomial of C over the prime field
intrinsic get_exact_random_l_torsion(C::Crv, fields::SeqEnum, gal_groups::SeqEnum, num_point_curve::SeqEnum, l_d_m::SeqEnum, char_poly::RngUPolElt: add_alg := 1, kummer := []) -> RngMPol
{}
	l := l_d_m[1];
	d := l_d_m[2];
	m := l_d_m[3];
	K<a> := SplittingField(NumberField(char_poly));
	i := 0;
	err := 0;

	ff_q := fields[1];
	while true do
		

		D0 := random_point_fast(C, fields, gal_groups, num_point_curve);
		if kummer ne [] then
			D0 := apply_kummer_map(D0, kummer, C);
			if is_zero_jac(Multiply(D0, C, l^d), C) eq false then
				error Error("Not l^d torsion");
			end if;
			return D0;
		end if;
		try
			D1 :=  Multiply(D0, C, m: add_alg := add_alg);
		catch e
			err +:= 1;
		end try;

		if err eq 1 then
			err := 0;
			continue;
		end if;

		i +:= 1;

		if i mod 100 eq 0 then
			print i;
		end if;

		exact_pow := 1;
		D2 := D1;
		while true do
			D2 := Multiply(D2, C, l: add_alg := add_alg);
			if is_zero_jac(D2, C: add_alg := add_alg) then
				break;
			end if;
			exact_pow +:= 1;
		end while;

		if exact_pow gt d then
			return Multiply(D1, C, l^(exact_pow - d));
		end if;
	
		if exact_pow eq d then
			return D1;
		end if;

	end while;

end intrinsic;


// Change ind to deal with arbitrary genus
// Checks if element given by basis is 0 on l^d torsion point D
// Assumes addition law 1 for this step
intrinsic is_zero_on_l_torsion_point(basis::SeqEnum, gen::FldNumElt, l_d::SeqEnum, D::RngMPol, C::Crv, ff_q::FldFin) ->BoolElt
{}
	l := l_d[1];
	d := l_d[2];
	p := Characteristic(ff_q);
	j := 0;
	for alpha in basis do
		K := Parent(gen);
		O := MaximalOrder(K);
		coeffs := element_to_coeffs(alpha, gen);
		n := coeffs[#coeffs];

		i := size_of_prime_power(n, l);

		if i lt d then
			continue;
		end if;

		g_poly_ring := Parent(Generators(D)[1]);
		g_x := Name(g_poly_ring,1);
		g_y := Name(g_poly_ring,2);

		Q_i := ideal<g_poly_ring | 1>;

		// Construct Q_i incrementally
		for ind in [1..6] do
			if coeffs[ind] ne 0 then
				P_i := Multiply(frob_ideal(D,p^(ind-1)), C, coeffs[ind]: add_alg := 1);

				Q_i := Addition(P_i, Q_i,C: add_alg := 1);
			end if;
		end for; 

		if is_zero_jac(Q_i,C: add_alg := 1) ne true then
				
			return false;
		end if;
                j := j + 1;

	end for;

	return true;
end intrinsic;



intrinsic num_curve_points_from_frob(K::FldNum, char_poly::RngUPolElt, k::RngIntElt, q::RngIntElt) -> RngIntElt
{}
	
	R, h := ChangeRing(Parent(char_poly), K);
	roots := Roots(h(char_poly));
	sum := 0;
	for root in roots do
		sum +:= (root[1]^k)*root[2];
	end for;
	try
		return IntegerRing() ! (q^k + 1 -sum);
	catch e
		print IntegerRing() ! q^k + 1 -sum;
		error e;
	end try;

end intrinsic;


// From avisogenies
intrinsic GetFullTorsionExtension(l::RngIntElt,frob::RngUPolElt) -> RngIntElt
{}
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
end intrinsic;

intrinsic is_defined_over_subfield(P::RngMPol, C::Crv, ff_q::FldFin) -> BoolElt
{}
	if is_zero_jac(P, C) eq true then
		return true;
	end if;
	points := ideal_to_divisor(P, C);
	l := Parent(points[1][1]);	
        _, auts := GaloisGroup(l,ff_q);
        for aut_elt in auts do
                aut := hom<l->l|aut_elt>;
                for point in points do
                        x_val_conj := aut(point[1]);
                        y_val_conj := aut(point[2]);
                        is_conj := false;
                        for point in points do
                                if x_val_conj eq point[1] and y_val_conj eq point[2] then
                                        is_conj := true;
                                        break;
                                end if;
                        end for;
                        if is_conj eq false then
                                return false;
                        end if;
                end for;
        end for;

        return true;
end intrinsic;



intrinsic max_l_valuation(basis::SeqEnum, gen::FldNumElt, l::RngIntElt) -> RngIntElt
{}

	d := 0;
	for alpha in basis do
		
		CC := ComplexField();
		pis := Conjugates(gen);
		alphas := Conjugates(alpha);

		coeffs := IntegerRelation([CC ! 1, pis[1], pis[1]^2, pis[1]^3, pis[1]^4, pis[1]^5, -alphas[1]]);
		n := coeffs[#coeffs];

		i := size_of_prime_power(n, l);
		d := Maximum(d,i);
	end for;

	return d;
end intrinsic;

intrinsic init_random_point_fast_data(char_poly::RngUPolElt, C::Crv, ff_q::FldFin) -> SeqEnum, SeqEnum, SeqEnum
{}
	K<a> := SplittingField(NumberField(char_poly));

	k_prime := CoefficientRing(Parent(DefiningPolynomial(C)));

	k2<b> := ext<ff_q|2 : Optimize := false, Sparse := false>;
	k3<c> := ext<ff_q|3 : Optimize := false, Sparse := false>;
	_, maps_k2 := GaloisGroup(k2,ff_q);
	_, maps_k3 := GaloisGroup(k3,ff_q);
	h2 := hom<k2->k2|maps_k2[2]>;
	h3 := hom<k3->k3|maps_k3[2]>;


	n1 := num_curve_points_from_frob(K,char_poly,1,Characteristic(k_prime));
	n2 := num_curve_points_from_frob(K,char_poly,2,Characteristic(k_prime));
	n3 := num_curve_points_from_frob(K,char_poly,3,Characteristic(k_prime));

	return [ff_q,k2,k3], [h2,h3], [n1,n2,n3];
end intrinsic;


intrinsic is_linearly_ind_torsion(basis_l_d::SeqEnum, C::Crv, l::RngIntElt, ff_q::FldFin : add_alg := 1) -> BoolElt
{}
	linear_combos_of_l_tors := [];
	rels := [];
	linearly_ind := [];
	ff_l := FiniteField(l);
	for i in [1..#basis_l_d] do
		P := basis_l_d[i];
		in_list, index := point_in_list(linear_combos_of_l_tors, P, C);
		if in_list eq true then
			base_l := IntegerToSequence(index-1, l);
			rel := [ff_l ! 0: x in [1..#basis_l_d]];
			for ind in [1..#base_l] do
				rel[linearly_ind[ind]] := ff_l ! base_l[ind];
			end for;
			rel[i] := ff_l ! -1;
			Append(~rels, rel);
			continue;
		end if;
		print "Num tors basis: ", i;
		Include(~linearly_ind, i);
		linear_combos_of_l_tors := generate_linear_combos(C, ff_q, linear_combos_of_l_tors, P: add_alg := add_alg);
	end for;

	if #rels gt 0 then
		return false, rels;
	else
		return true, rels;
	end if;	
end intrinsic;

intrinsic is_torsion_basis_brute_force(basis_l_d::SeqEnum, C::Crv, l::RngIntElt, ff_q::FldFin : add_alg := 1) -> BoolElt
{}
	g := 3;
	if #basis_l_d ne 2*g then
		return false;
	end if;
	linear_combos_of_l_tors := [];
	for i in [1..2*g] do
		print "Num tors basis: ", i;
		P := basis_l_d[i];
		if point_in_list(linear_combos_of_l_tors, P, C) eq true then
			return false;
		end if;
		if i eq 2*g then
			return true;
		end if;
		linear_combos_of_l_tors := generate_linear_combos(C, ff_q, linear_combos_of_l_tors, P: add_alg := add_alg);
	end for;
	
end intrinsic;

intrinsic get_torsion_brute_force(C::Crv, l_i::SeqEnum, m::RngIntElt, char_poly::RngUPolElt, ff_q::FldFin, ff_q_cm::FldFin: add_alg := 1, kummer := []) ->SeqEnum
{}
	g := 3;

	l := l_i[1];
	i := l_i[2];
	basis_l := [];
	linear_combos_of_l_tors := [];

	basis_l_d := [];
	fields, gal_groups, num_points_curve := init_random_point_fast_data(char_poly, C, ff_q);
	num_tried := 0;
	while true do

		P := get_exact_random_l_torsion(C, fields, gal_groups, num_points_curve, [l,i,m], char_poly: add_alg := add_alg, kummer := kummer);
		num_tried +:= 1;
		if (num_tried mod 100) eq 0 then
			print num_tried;
		end if;
		Q := Multiply(P, C, l^(i-1): add_alg := add_alg);

		if point_in_list(linear_combos_of_l_tors, Q, C: add_alg := add_alg) eq false then
			Include(~basis_l, Q);
			Include(~basis_l_d, P);

			print "Num Tried : ", num_tried;
			print "Num Basis of l tors: ", #basis_l;

			if #basis_l_d eq 2*g then
				break;
			end if;
			
			// Store linear combinations of l-torsion. Note, we do not store
			// linear combos of l^d torsion as it is more expensive.
			linear_combos_of_l_tors := generate_linear_combos(C, ff_q, linear_combos_of_l_tors, Q: add_alg := add_alg);
		end if;

	end while;

	return basis_l_d;
end intrinsic;

intrinsic linear_combo(list::SeqEnum, combo::SeqEnum, C::Crv, ff_q::FldFin: add_alg := 1) -> RngMPol
{}
	P := zero_jac(C, ff_q: add_alg := add_alg);
	if #list ne #combo then
		Error("Number of elements in list must match Number of elements in combo");
	end if;
	for ind in [1..#combo] do
		P := Addition(P, Multiply(list[ind], C, IntegerRing() ! combo[ind]: add_alg := add_alg), C: add_alg := add_alg);
	end for;
	return P;
end intrinsic;

intrinsic test_relation(list::SeqEnum, relation::SeqEnum, C::Crv, ff_q::FldFin: add_alg := 1) -> BoolElt
{}
	P := linear_combo(list, relation, C, ff_q: add_alg := 1);
	if is_zero_jac(P, C: add_alg := add_alg) then
		return true;
	else
		return false;
	end if;
		
end intrinsic;

intrinsic find_relations(A::AlgMatElt, basis_l::SeqEnum, l::RngIntElt, C::Crv, ff_q::FldFin: add_alg := 1) -> SeqEnum
{}

	null := NullspaceMatrix(Transpose(A));
	null := EchelonForm(null);
	print null;
	relations := [];
	potential_rels := [];
	for vector in RowSequence(null) do
		if test_relation(basis_l, vector, C, ff_q: add_alg := add_alg) eq true then
			Append(~relations, vector);
		else
			Append(~potential_rels, vector);
		end if;
	end for;
	gens := [];
	for rel in potential_rels do
		Append(~gens, linear_combo(basis_l, rel, C, ff_q: add_alg := add_alg));
	end for;
	_, gen_rels := is_linearly_ind_torsion(gens, C, l, ff_q: add_alg := 1);
	if gen_rels ne [] then
		rels_matrix :=  Matrix(gen_rels)*Matrix(potential_rels);
		relations := relations cat RowSequence(rels_matrix);
	end if;
	
	return relations;
end intrinsic;

intrinsic get_torsion_mixed(C::Crv, l_i::SeqEnum, m::RngIntElt, char_poly::RngUPolElt, ff_q::FldFin, ff_q_CM::FldFin : add_alg := 1, kummer := []) -> SeqEnum
{}
	l := l_i[1];
	i := l_i[2];
	g := 3;

	basis_l := [];
	basis_l_zeroes := [];
	linear_combos_of_l_tors := [];

	basis_l_d := [];
	fields, gal_groups, num_points_curve := init_random_point_fast_data(char_poly, C, ff_q);
	num_tried := 0;
	while true do

		P := get_exact_random_l_torsion(C, fields, gal_groups, num_points_curve, [l, i, m], char_poly: add_alg := add_alg, kummer := kummer);
		num_tried +:= 1;
		if (num_tried mod 100) eq 0 then
			print num_tried;
		end if;
		Q := Multiply(P, C, l^(i-1): add_alg := add_alg);

		if point_in_list(linear_combos_of_l_tors, Q, C: add_alg := add_alg) eq false then
			Include(~basis_l, Q);
			Include(~basis_l_d, P);
			Append(~basis_l_zeroes, ideal_to_divisor(Q, C));
			print "Num Tried : ", num_tried;
			print "Num Basis of l tors: ", #basis_l;

			if #basis_l_d lt (2*g)-1 then
			
			// Store linear combinations of l-torsion. Note, we do not store
			// linear combos of l^d torsion as it is more expensive.
				linear_combos_of_l_tors := generate_linear_combos(C, ff_q, linear_combos_of_l_tors, Q: add_alg := add_alg);
			end if;
		else
			continue;
		end if;

		if #basis_l_d lt 2*g then
			continue;
		end if;
		A := compute_pairing_matrix(basis_l, l, C: basis_l_divs := basis_l_zeroes);
		print A;
		is_inv := IsInvertible(A);
		if is_inv eq true then
			print "NumTried: ", num_tried;
			print "IsInv";
			return basis_l_d;
		else
			Remove(~basis_l_d, 2*g);
			Remove(~basis_l, 2*g);
			Remove(~basis_l_zeroes, 2*g);
		end if;
	end while;

	return basis_l_d;

end intrinsic;


intrinsic get_torsion_pairing(C::Crv, l_i::SeqEnum, m::RngIntElt, char_poly::RngUPolElt, ff_q::FldFin, ff_q_CM::FldFin: add_alg := 1, kummer := []) -> SeqEnum
{}
	l := l_i[1];
	i := l_i[2];
		
	g := 3;

	basis_l := [];
	basis_l_zeroes := [];
	basis_l_d := [];
	fields, gal_groups, num_points_curve := init_random_point_fast_data(char_poly, C, ff_q);
	linear_combos_of_tors := [];
	num_ind := 0;
	num_tried := 0;
	while true do
		while true do

			P := get_exact_random_l_torsion(C, fields, gal_groups, num_points_curve, [l, i, m], char_poly: add_alg := add_alg, kummer := kummer);
			num_tried +:= 1;
			Q := Multiply(P, C, l^(i-1): add_alg := add_alg);

			if point_in_list(linear_combos_of_tors, Q, C: add_alg := add_alg) eq false then
				Include(~basis_l, Q);
				Include(~basis_l_d, P);

				print "Num Basis of l tors: ", #basis_l;

				if #basis_l_d eq 2*g then
					break;
				end if;
				
			end if;

		end while;
		for i in [(#basis_l_zeroes+1)..#basis_l] do
			Append(~basis_l_zeroes, ideal_to_divisor(basis_l[i], C));
		end for;
		A := compute_pairing_matrix(basis_l, l, C: basis_l_divs := basis_l_zeroes);
		print A;
		is_inv := IsInvertible(A);
		if is_inv eq true then
			print "NumTried: ", num_tried;
			print "IsInv";
			return basis_l_d;
		else
			relations := find_relations(A, basis_l, l, C, ff_q: add_alg := add_alg); 	
			print "Num relations: ", #relations;
			indices_to_delete := {};
			
			for vector in relations do
				for j in [1..#vector] do
					if vector[j] ne 0 and (j in indices_to_delete) eq false then
						Include(~indices_to_delete, j);
						break;
					end if;
				end for;
			end for;
			indices_to_delete := Sort(IndexedSetToSequence(SetToIndexedSet(indices_to_delete)));
			print indices_to_delete;
			if indices_to_delete eq [] then
				print "NumTried: ", num_tried;
				return basis_l_d;
			end if;
			j := #indices_to_delete;
			while j gt 0 do
				Remove(~basis_l_d, indices_to_delete[j]);
				Remove(~basis_l, indices_to_delete[j]);
				Remove(~basis_l_zeroes, indices_to_delete[j]);
				j := j - 1;
			end while;
		end if;
	end while;
end intrinsic;

intrinsic get_torsion(C::Crv, l_i::SeqEnum, m::RngIntElt, char_poly::RngUPolElt, ff_q::FldFin: add_alg := 1, kummer := []) -> SeqEnum
{}
	l := l_i[1];
	i := l_i[2];
	if l le 3 then	
		basis_l_d := get_torsion_brute_force(C, [l, i], m, char_poly, ff_q, ff_q: add_alg := add_alg, kummer := kummer); 
	else
		basis_l_d := get_torsion_pairing(C, [l, i], m, char_poly, ff_q, ff_q: add_alg := add_alg, kummer := kummer);
	end if;
	return basis_l_d;
end intrinsic;

intrinsic check_endomorphisms(C::Crv, l_i_k::SeqEnum, ff_p::FldFin, char_poly::RngUPolElt, gen::FldNumElt, basis::SeqEnum : add_alg := 1) -> BoolElt
{}
	l := l_i_k[1];
	i := l_i_k[2];
	k := l_i_k[3];
	K<pi> := NumberField(char_poly);
	if i eq 1 then // If field of defn of l-torsion hasn't been checked
		k_prime := k;
		kummer := get_kummer_map(pi, k_prime, l);
	else
		k_prime := deg_of_field_of_defn_of_n_tors(char_poly,l)*l^(i-1);
		kummer := [];
	end if;

	num_pts := num_points_on_jac(char_poly, k_prime);

	ff_q := ext<ff_p| k_prime : Optimize := false, Sparse := false>;
	print "Extension Degree: ", k_prime;
	if i eq 1 then
		deg := deg_of_field_of_defn_of_n_tors(char_poly,l);
		print "Degree of Extension for CM: ", deg;
		ff_q_CM := sub<ff_q|deg : Optimize := false, Sparse:= false>; // Field of defn if Jac(C) has CM by \cO_K
		
		num_pts_CM := num_points_on_jac(char_poly, deg_of_field_of_defn_of_n_tors(char_poly,l));
		if (num_pts_CM mod l) ne 0 then
			print "Num_pts_mod_l: ", num_pts_CM mod l;
			return false;
		end if;
	end if;

	s := size_of_prime_power(num_pts, l);
	m := IntegerRing() ! (num_pts/(l^s));

	basis_l_d := get_torsion(C, [l, i], m, char_poly, ff_q: add_alg := 1, kummer := kummer);
	for P in basis_l_d do
		if i eq 1 then
			if is_defined_over_subfield(P, C, ff_q_CM) eq false then
				return false;
			end if;
		end if;
		if is_zero_on_l_torsion_point(basis, gen, [l, i], P, C, ff_q) eq false then
			return false;
		end if;
	end for;
	
	return true;
end intrinsic;
 
intrinsic find_n_for_suborder(E::RngOrd, alpha::FldNumElt) -> RngIntElt
{}
	n := 1;
	while true do
		if n*alpha in E then
			return n;
		end if;
		n +:= 1;
	end while;
end intrinsic;


intrinsic size_of_prime_power(num::RngIntElt, l::RngIntElt) -> RngIntElt
{}
	s := 0;
	while true do
		if num mod l^(s+1) ne 0 then
			return s;
		end if;
		s := s + 1;
	end while;
end intrinsic;


intrinsic num_points_on_jac(char_poly::RngUPolElt, m::RngIntElt) -> RngIntElt
{}
	K<gen> := NumberField(char_poly);
	poly := CharacteristicPolynomial(gen^m);

	return IntegerRing() ! Evaluate(poly, 1);
end intrinsic;


intrinsic random_point_jacobian_FO(C::Crv, k::FldFin) -> SeqEnum
{}
	g := 3;
	R<x> := PolynomialRing(k);
	f_0 := 0;
	f_coeffs := coefficients_of_picard_curve(C,k);

	for j in [1..#(f_coeffs)] do
		f_0 +:= (R ! f_coeffs[j])*x^(j-1);
	end for;

	f := f_0;
	while true do
		v := 0;
		for i in [1..3] do
			v +:= Random(k)*x^(i-1);
		end for;
		factors := Factorization(v^3 - f);
		for fact in factors do
			u := fact[1]^fact[2];
			if Degree(u) eq 3 and Degree(u) gt Degree(v) and Degree(u) le g then
				return [u, v];
			end if;
		end for;
	end while;
end intrinsic;

intrinsic get_random_picard_point(C::Crv, k::FldFin) -> SeqEnum
{}
	f := coefficients_of_picard_curve(C, k);
	R<x> := PolynomialRing(k);
	f := f[1] + f[2]*x + f[3]*x^2 + x^4; // Assumed in reduced form

	while true do
		a := Random(k);
		is_root, b := IsPower(Evaluate(f, a),3);
		if is_root eq true then
			return [a,b];
		end if;
	end while;
end intrinsic;

intrinsic random_point_fast(C::Crv, fields::SeqEnum, gal_groups::SeqEnum, num_point_curve::SeqEnum) -> RngMPol
{}
	// k_div corresponds to divisors for which every point in the support is a point over the base field
	num_deg_1_k_div := num_point_curve[1] -1; // -1 for pt at infinity
	num_deg_2_k_div := (num_point_curve[1] -1)^2;
	num_k_div := Binomial(num_point_curve[1],3) + num_point_curve[1]^2;
	num_deg_2_k2_div := (num_point_curve[2]-num_point_curve[1])/2;
	// k2_div corresponds to divisors for which every point in the support is a point over a degree 2 extension of the base field
	num_k2_div := num_point_curve[1]*(num_point_curve[2]-num_point_curve[1])/2; 
	// k3_div corresponds to divisors for which every point in the support is a point over a degree 3 extension of the base field
	num_k3_div := (num_point_curve[3]-num_point_curve[1])/3; 

	total := num_k_div + num_k2_div + num_k3_div;
	r := Random(0, IntegerRing() ! total);
	pts := [];

	num_pts := 0;
	k := 0;

	g_poly_ring<g_x,g_y> := PolynomialRing(fields[1],2,"weight", [3,4, 0,1]);
	//print Grading(g_poly_ring);
	x_list := [];
	y_polys := [];

	// Find a random divisor as a sum of points on the curve with probability proportional to
	// the number of k_divs, k2_divs and k3_divs respectively.
	if r eq 0 then
		return ideal<g_poly_ring|1>;
	end if;

	if r le num_k_div then
		k := fields[1];
		if r eq 0 then
			num_pts := 0;
		else
			if r le num_deg_1_k_div then
				num_pts := 1;
			else
				if r le num_deg_2_k_div then
					num_pts := 2;
				else
					num_pts := 3;
				end if;
			end if;
		end if;
		ff_q := fields[1];
		for i in [1..num_pts] do
			p := get_random_picard_point(C,fields[1]);
			Append(~pts, p);
		end for;	
	end if;

	if r gt num_k_div and r le num_k2_div + num_k_div then
		k := fields[2];		
		aut := gal_groups[1];
		while true do
			p := get_random_picard_point(C,fields[2]);
			if aut(p[1]) ne p[1] or aut(p[2]) ne p[2] then
				break;
			end if;
		end while;

		Append(~pts, p);
		Append(~pts, [aut(p[1]), aut(p[2])]);
		if (r - num_k_div) gt num_deg_2_k2_div then
			p := get_random_picard_point(C,fields[1]);
			Append(~pts, p);
		end if;
	end if;

	if r gt (num_k2_div + num_k_div) then
		k := fields[3];
		aut := gal_groups[2];
		while true do
			p := get_random_picard_point(C,fields[3]);
			if aut(p[1]) ne p[1] or aut(p[2]) ne p[2] then
				break;
			end if;
		end while;

		Append(~pts, p);
		Append(~pts, [aut(p[1]), aut(p[2])]);
		Append(~pts, [aut(aut(p[1])), aut(aut(p[2]))]);
	end if;

	// Construct generators for the ideal corresponding to the random divisor
	R<x,y> := PolynomialRing(k,2);

	for pt in pts do
		x0 := pt[1];
		y0 := 1;
		for pt1 in pts do
			if pt1[1] eq x0 then
				y0 := y0*(y - pt1[2]);
			end if; 
		end for;
		if x0 in x_list eq false then
			Append (~x_list, x0);
		end if;
		Append(~y_polys, y0);
	end for;

	u := 1;
	w := 1;
	for pt in pts do
		u := u*(x-pt[1]);
	end for;
	if #x_list eq 1 then
		if #pts eq 1 then
			w := y_polys[1];
		end if;
		if #pts eq 2 or #pts eq 3 then
			w := y_polys[1];
		end if;
	end if;
	if #x_list eq 2 then
		if #pts eq 2 then
			w := y - Interpolation(x_list, [R ! pts[1][2], pts[2][2]], 1);
		end if;
		if #pts eq 3 then
			w := (x - x_list[2])/(x_list[1] - x_list[2])*y_polys[1] + (x - x_list[1])/(x_list[2] - x_list[1])*y_polys[2];
		end if;
	end if;
	if #x_list eq 3 then
		w := y - Interpolation(x_list, [R ! pts[1][2], pts[2][2], pts[3][2]], 1);
	end if;

	u := g_poly_ring ! u;
	w := g_poly_ring ! w;
	
	return ideal<g_poly_ring|u, w>;
end intrinsic;

intrinsic random_point(C::Crv, k::FldFin) -> SeqEnum
{}
	g := 3;
	R<x> := PolynomialRing(k);
	f_0 := 0;
	f_coeffs := coefficients_of_picard_curve(C,k);

	for j in [1..#(f_coeffs)] do
		f_0 +:= (R ! f_coeffs[j])*x^(j-1);
	end for;

	f := f_0;
	while true do
		u := 0;
		for i in [1..2] do
			u +:= Random(k)*x^(i-1);
		end for;
		u +:= x^3;
		factors := Factorization(u);
		k_prime := k;
		for fact in factors do
			if Degree(fact[1]) gt 1 then
				k_prime := ext<k|fact[1]>;
				break;
			end if;
		end for;
		R_prime<x_prime>, h := ChangeRing(R, k_prime);
		roots := Roots(h(u));
		x_vals := [];
		y_vals := [];
		f := h(f);
		test := false;
		v := 0;
		for root in roots do
			if IsPower(Evaluate(f, root[1]),3) eq false then
				test := true;
				break;
			else
				_, y_i := IsPower(Evaluate(f, root[1]),3);
				Append(~x_vals, root[1]);
				Append(~y_vals, y_i);
			end if;
		end for;
			
		if test eq false then
			v := Interpolation(x_vals, y_vals);
			//print u div v^3 - f;
			return [u,v];
		end if;
	end while;
end intrinsic;


intrinsic point_in_list(list::SeqEnum, P::RngMPol, C::Crv: add_alg := 1) -> BoolElt, RngIntElt
{}
	ind := 1;
	for Q in list do
		if #Generators(Q) eq #Generators(P) then
			gens_equal := true;
			for i in [1..#Generators(P)] do
				if Generators(Q)[i] in Generators(P) eq false then
					gens_equal := false;
				end if;
			end for;
			if gens_equal eq true then
				return true, ind;
			end if;
		end if;
		ind +:= 1;
	end for;

	return false, 0;
end intrinsic;


intrinsic generate_linear_combos(C::Crv, ff_q::FldFin, points::SeqEnum, P::RngMPol: add_alg := 1) -> SeqEnum
{}
	i := 0;
	combos := [];
	if points eq [] then
		Append(~points, zero_jac(C, ff_q));
	end if;
	while true do
		P_i := Multiply(P, C, i: add_alg := add_alg);
		if is_zero_jac(P_i, C: add_alg := add_alg) and i gt 0 then
			return combos;
		end if;
		for point in points do
			Include(~combos, Addition(point, P_i, C: add_alg := add_alg));
		end for;
		i +:= 1;
	end while;	

end intrinsic;


// Finds a random point on the Jacobian of a picard curve. 
intrinsic random_point_jacobian(C::Crv, k::FldFin : add_alg := 1) -> RngMPol
{}

	if add_alg eq 1 then
		g_poly_ring<g_x,g_y> := PolynomialRing(k,2,"weight", [3,4, 0,1]);
		D := random_point_jacobian_FO(C, k);
		u := D[1];
		v := D[2];
		u_temp := g_poly_ring ! 0;
		v_temp := g_poly_ring ! 0; 
		for i in [1..(Degree(u)+1)] do
			u_temp +:= Coefficients(u)[i]*g_x^(i-1);
		end for;
		for i in [1..(Degree(v)+1)] do
			v_temp +:= Coefficients(v)[i]*g_x^(i-1);
		end for;
		//print IsPrincipal(ideal< g_poly_ring | u_temp, g_y - v_temp>);
		return ideal< g_poly_ring | u_temp, g_y - v_temp>;
	end if;

	return random_point_jacobian_FO(C,k);
end intrinsic;


