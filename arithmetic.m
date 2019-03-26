import "addition.m" : addition, doubling;
import "scalarproduct.m" : Multi;

// Wrapper function. Intended for use with more general curves.
intrinsic Addition(D1::RngMPol, D2::RngMPol, C::Crv : add_alg := 1) -> SeqEnum
{}
	try
		Div3, n_d := picard_add(D1, D2, C: add_alg := add_alg);
	catch e
		print D1;
		try // If add_alg is not 1
			if is_zero_jac(Addition(D1, D2, C), C) eq true then
				return [0,0];
			else				
				error Error(e);
			end if;
		catch e2
			error Error(e);
		end try;
	end try;
	return Div3, n_d;
end intrinsic;

// Returns affine coordinate ring of C
intrinsic affine_ring(C::Crv, k::FldFin) -> SeqEnum
{}
	l<x> := FunctionField(k);
	R<y> := PolynomialRing(l);

	
	f_0 := 0;
	f_coeffs := coefficients_of_picard_curve(C,k);

	for j in [1..#(f_coeffs)] do
		f_0 +:= (R ! f_coeffs[j])*x^(j-1);
	end for;

	f := f_0;
	K := FunctionField(y^3 - f);
	O := MaximalOrderFinite(K);
	return O, x, y;
end intrinsic;

// For Picard curve C:y^3 = f(x), returns coefficients of f(x) in order
// of increasing degree
intrinsic coefficients_of_picard_curve(C::Crv, ff_q::FldFin) -> SeqEnum
{}
	f := DefiningPolynomial(C);

	x_f := Name(f,1);

	f0 := -ff_q ! MonomialCoefficient(f, 1);
	f1 := -ff_q ! MonomialCoefficient(f, x_f);
	f2 := -ff_q ! MonomialCoefficient(f, x_f^2);
	f3 := -ff_q ! MonomialCoefficient(f, x_f^3);
	f4 := 1;

	return [f0, f1, f2, f3, f4];
end intrinsic;

intrinsic divisor_poly_to_tuple(u::RngUPolElt, v::RngUPolElt) -> SeqEnum
{}
	return [Coefficient(u, 0), Coefficient(u, 1), Coefficient(u, 2), Coefficient(v, 0), Coefficient(v, 1), Coefficient(v, 2)];
end intrinsic;

// Wrapper function. Intended for use with more general curves.
intrinsic inverse(D::RngMPol, C::Crv : add_alg := 1) -> RngMPol
{}
	
	D_inv := picard_inverse(D, C: add_alg := add_alg);

	return D_inv;
end intrinsic;

// The add_alg := 1 part of this code is very specific to the Picard case and would need
// changing for the general non-hyperelliptic case.
// Finds inverse of point D
intrinsic picard_inverse(D::RngMPol, C::Crv : add_alg := 1) -> RngMPol
{}
	if add_alg eq 1 then
		f := 0;
		g_poly_ring := Parent(Generators(D)[1]);
		g_x := Name(g_poly_ring,1);
		g_y := Name(g_poly_ring,2);
		ff_q := CoefficientRing(g_poly_ring);

		f_coeffs := coefficients_of_picard_curve(C, ff_q);
		for i in [1..#f_coeffs] do
			f +:= f_coeffs[i]*g_x^(i-1);
		end for;
		f := g_y^3 - f;
		P := ideal< g_poly_ring | f >;
		D, n := jInverse(D, P, g_poly_ring);
		return D;
	end if;
	
	if add_alg eq 2 then
		D0 := divisor_poly_to_tuple(D[1], D[2]);


		for elem in D0 do
			if elem ne 0 then
				ff_q := Parent(elem);
				break;
			end if;
		end for;

		f_coeffs := coefficients_of_picard_curve(C, ff_q);
		f0 := f_coeffs[1];
		f1 := f_coeffs[2];
		f2 := f_coeffs[3];

		R<x> := PolynomialRing(Parent(D0[1]));

		u := D0[1] + D0[2]*x + D0[3]*x^2 + x^3;
		v := D0[4] + D0[5]*x + D0[6]*x^2;
		
		f := x^4 + f2*x^2 + f1*x + f0;
		q := ExactQuotient(v^3-f, u);
		q := q/Coefficient(q, 3);

		return [q,v];
	end if;
end intrinsic;

// Given divisor D representing point Jac(C), return two polynomials,
// u(x), v(x,y) such that D = <u, v>.
intrinsic mumford_rep(D::RngMPol, C::Crv, ff_q_prime::FldFin) -> RngMPol
{}
	pts := ideal_to_divisor(D,C);
	l := Parent(pts[1][1]);
	R<x,y> := PolynomialRing(l,2);
	x_list := [];
	y_polys := [];
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

	g_poly_ring<g_x,g_y> := PolynomialRing(ff_q_prime,2,"weight", [3,4, 0,1]);
	return ideal<g_poly_ring| g_poly_ring ! u, g_poly_ring ! w>;
end intrinsic;

// Convert point on Jac(C) represented as ideal, to divisor represented as points
// on C
intrinsic ideal_to_divisor(D::RngMPol,C::Crv) -> SeqEnum
{}

	g_poly_ring := Parent(Generators(D)[1]);
	g_x := Name(g_poly_ring,1);
	g_y := Name(g_poly_ring,2);
	ff_q := Parent(MonomialCoefficient(Generators(D)[1],g_x^0*g_y^0));

	f := 0;
	f_coeffs := coefficients_of_picard_curve(C, ff_q);
	for i in [1..#f_coeffs] do
		f +:= f_coeffs[i]*g_x^(i-1);
	end for;


	g_poly_ring := Parent(Generators(D)[1]);
	g_x := Name(g_poly_ring,1);
	g_y := Name(g_poly_ring,2);
	ff_q := Parent(MonomialCoefficient(Generators(D)[1],g_x^0*g_y^0));

	k<a> := FunctionField(ff_q);
	R<b> := PolynomialRing(k);

	f := 0;
	f_coeffs := coefficients_of_picard_curve(C, ff_q);
	for i in [1..#f_coeffs] do
		f +:= f_coeffs[i]*a^(i-1);
	end for;

	L<c> := ext<k | b^3 - f>;
	O := MaximalOrderFinite(L);
	gens := Generators(D);


	fun_field_gens := [];
		
	for gen in gens do
		fun_field_gen := 0;
		for i in [0..(#Coefficients(gen,g_x)-1)] do
			for j in [0..(#Coefficients(gen,g_y)-1)] do
					fun_field_gen +:= (ff_q ! MonomialCoefficient(gen,g_x^i*g_y^j))*a^i*c^j;
			end for;
		end for;
		Append(~fun_field_gens,fun_field_gen);
	end for;

	I := ideal<O | fun_field_gens>;
	l := ext<ff_q|6 : Optimize := false, Sparse := false>;
	points := [];
	for fact in Factorization(I) do
		for index in [1..fact[2]] do
			one_gen, sec_gen := TwoElement(fact[1]);
			R2<t1> := PolynomialRing(k);
			R3<x,y> := PolynomialRing(l,2);
			R4<t2> := PolynomialRing(l);
			map := hom<L -> R2|t1>;
			map2 := hom<k -> R3|x>;
			sec_gen_map := map(sec_gen);
			map3 := hom<k -> R4|t2>;
			first_gen := map3(one_gen);
	
			roots := Roots(first_gen);
			sec_gen := 0;
			
			for i in [1..#Coefficients(sec_gen_map)] do
				sec_gen +:= map2(Coefficient(sec_gen_map,i-1))*y^(i-1);
			end for;
	
			for fact in Factorization(first_gen) do
				factor := fact[1];
				x_val := Roots(factor)[1][1];

				y_val_poly := Evaluate(sec_gen, 'x', x_val);
				y_val_univ_poly := 0;

				for i in [0..#Coefficients(y_val_poly, 'y')-1] do
					y_val_univ_poly +:= (l ! Coefficient(y_val_poly, 'y', i))*t2^i;
				end for;
				y_vals := Roots(y_val_univ_poly);

				f := 0;
				f_coeffs := coefficients_of_picard_curve(C, ff_q);
				for i in [1..#f_coeffs] do
					f +:= f_coeffs[i]*t2^(i-1);
				end for;
				num_roots := 0;
				for y_val in y_vals do
					if y_val[1]^3 eq Evaluate(f, x_val) then
						for i in [1..Minimum(y_val[2], Roots(factor)[1][2])] do
							num_roots +:= 1;
							Append(~points, [x_val, y_val[1]]);
						end for;
					end if;
				end for;
				if num_roots ne Roots(factor)[1][2] then
					return false;
				end if;
			end for;
		end for;
	end for;

	return points;


end intrinsic;


// Determine if divisor D0 represented as an ideal, is typical in the sense of Flon-Oyono
intrinsic is_typical_div_multi(D0::RngMPol,C::Crv,m::RngInt : add_alg := 1) -> BoolElt, RngMPol
{}
	try
		D1 := Multiply(D0, C, m: add_alg := add_alg);
	catch e
		print e;
		return false, 0;
	end try;

	return true, D1;
end intrinsic;


intrinsic is_equal(P::RngMPol, Q::RngMPol: add_alg := 1) -> BoolElt
{}
	if #Generators(Q) eq #Generators(P) then
		for i in [1..#Generators(P)] do
			if Generators(Q)[i] in Generators(P) eq false then
				return false;
			end if;
		end for;
		
		return true;
	end if;

	return false;
end intrinsic;

intrinsic evaluate_function(zeroes::SeqEnum, poles::SeqEnum, pairing_function::SeqEnum, C::Crv : add_alg := 1) -> FldFinElt
{}
        value := 1;
	i := 1;
	for n_d in pairing_function do
		num := n_d[1];
		denom := n_d[2];
        	for P in zeroes do
                	value := value*(Evaluate(num, P)/Evaluate(denom, P));
	        end for;
		for P in poles do
			value := value*(Evaluate(denom,P)/Evaluate(num, P));
		end for;
		i +:= 1;
	end for;
        return value;
end intrinsic;

intrinsic C_3_4(func::RngMPolElt) -> RngIntElt
{}
	order := 0;
	for mon in Monomials(func) do
		exponents := Exponents(mon);
		order := Maximum(order, 3*exponents[1] + 4*exponents[2]);	
	end for;
		
	return order;
end intrinsic;

intrinsic remove_pole_at_infty(pairing_function::SeqEnum) -> SeqEnum
{}
	g_poly_ring := Parent(pairing_function[1][1]);
	g_x := Name(g_poly_ring, 1);
	g_y := Name(g_poly_ring, 2);
	num := pairing_function[1][1];
	denom := pairing_function[1][2];
	C_3_4_order := C_3_4(num)-C_3_4(denom);
	if C_3_4_order gt 0 then
		num := num*g_x^(C_3_4_order);
		denom := denom*g_y*(C_3_4_order);
	else
		num := num*g_y*(-C_3_4_order);
		denom := denom*g_x*(-C_3_4_order);
	end if;

	return [[num, denom]];	
end intrinsic;

// Convert divisor div(D) into equivalent divisor with no pole at infinity
intrinsic move_divisor_away_from_infty(D::RngMPol, C::Crv) -> SeqEnum, SeqEnum
{}
	g_poly_ring := Parent(Generators(D)[1]);
	g_x := Name(g_poly_ring, 1);
	g_y := Name(g_poly_ring, 2);
	eff_D := ideal_to_divisor(D, C);
	n := #eff_D;
	eff_x := ideal_to_divisor(ideal<g_poly_ring|g_x^n>, C);
	eff_y := ideal_to_divisor(ideal<g_poly_ring|g_y^n>, C);
	zeroes := eff_x cat eff_D;
	return zeroes, eff_y;
end intrinsic;

// Computes pairing function for Weil pairing
intrinsic compute_pairing_function(D::RngMPol, m::RngIntElt, C::Crv : add_alg := 1, add_chain := 2) -> SeqEnum
{}
        g_poly_ring := Parent(Generators(D)[1]);
        I := ideal<g_poly_ring | 1>; // zero element
        A_i := I;
        D_pow_2i := D;
	pairing_function := [];
	h_i := [1,1];
	h_pow_2i := [1,1];
        i := m;
        while i gt 0 do
                if (i mod 2) eq 1 then
                        A_i, n_d := Addition(A_i, D_pow_2i, C : add_alg := add_alg);
                        i := (i-1) div 2;
			if h_i[1]*h_pow_2i[1]*n_d[1] eq h_i[2]*h_pow_2i[2]*n_d[2] then
				h_i := [g_poly_ring ! 1, g_poly_ring ! 1];
			else
				h_i := [h_i[1]*h_pow_2i[1]*n_d[1], h_i[2]*h_pow_2i[2]*n_d[2]];
			end if;
			Append(~pairing_function, h_i);
                else
                        i := i div 2;
                end if;
                if i gt 0 then
                        D_pow_2i, n_d := Addition(D_pow_2i, D_pow_2i, C: add_alg := add_alg);
			h_pow_2i := [h_pow_2i[1]^2*n_d[1], h_pow_2i[2]^2*n_d[2]];	
                end if;
        end while;

	return [pairing_function[#pairing_function]];
end intrinsic;

// For function f = n_d[1]/n_d[2], output div(f) as zeroes, poles
intrinsic function_to_divisor(n_d::SeqEnum, C::Crv) -> SeqEnum, SeqEnum
{}
	num := n_d[1];
	denom := n_d[2];
	g_poly_ring := Parent(num);
	if Degree(num) gt 0 then
		zeroes := ideal_to_divisor(ideal<g_poly_ring|num>, C);
	else
		zeroes := [];
	end if;
	if Degree(denom) gt 0 then
		poles := ideal_to_divisor(ideal<g_poly_ring|denom>, C);
	else
		poles := [];
	end if;
	return zeroes, poles;
end intrinsic;

intrinsic evaluate_at_infinity(zeroes::SeqEnum, poles::SeqEnum, pairing_function::SeqEnum, C::Crv) -> FldFinElt
{}
	g_poly_ring := Parent(pairing_function[1][1]);
	g_x := Name(g_poly_ring, 1);
	g_y := Name(g_poly_ring, 2);
	ff_q := Parent(zeroes[1][1]);
	ff_p := PrimeField(ff_q);
	gcd := GCD(Degree(ff_q), 12);
	if gcd eq 12 then
		l := ff_q;
	else	
		l := ext<ff_q|12 div gcd: Sparse := false, Optimize := false>; //Extension over which fourth and third degree polys will split	
	end if;
	while true do
		x_i := Random(ff_p);
		in_list := false;
		for point in (zeroes cat poles) do
			if point[1] eq (ff_q ! x_i) then
				in_list := true;
			end if;
		end for;
		if in_list eq true then
			continue;
		end if;
		break;
	end while;

	g := [[g_poly_ring ! 1,1]];
	g[1][1] := g_x - x_i;	
	f_coeffs := coefficients_of_picard_curve(C, ff_q);
	R<x> := PolynomialRing(l);
	f := 0;
	for i in [1..#f_coeffs] do
		f +:= f_coeffs[i]*x^(i-1);
	end for;
	y_cubed := Evaluate(f, x_i);
	R<y> := PolynomialRing(l);
	y_vals := Roots(y^3 - y_cubed);
	g_zeroes := [];
	g_poles := [];
	for root in y_vals do
		for i in [1..root[2]] do
			Append(~g_zeroes, [x_i, root[1]]);
		end for;
	end for;

	while true do
		y_i := Random(ff_p);
		in_list := false;
		for point in (zeroes cat poles cat g_zeroes) do
			if point[2] eq (ff_q ! y_i) then
				in_list := true;
			end if;
		end for;
		if in_list eq true then
			continue;
		end if;
		break;
	end while;
	g[1][2] := g_y - y_i;
	x_vals := Roots(f - y_i^3);
	for root in x_vals do
		for i in [1..root[2]] do
			Append(~g_poles, [root[1], y_i]);
		end for;
	end for;

	return evaluate_function(zeroes, poles, g, C)/evaluate_function(g_zeroes, g_poles, pairing_function, C); 

end intrinsic;

// Is not guaranteed to work if D1 and D2 do not have disjoint sets of zeroes!
intrinsic weil_pairing(D1::RngMPol, D2::RngMPol, m::RngIntElt, C::Crv : add_alg := 1, phi :=[], psi := [], D1_zeroes := [], D2_zeroes := [], div_at_infty := []) -> FldFinElt 
{}
	ff_m := FiniteField(m);
	for i in [1..m] do
		if is_equal(Multiply(D1,C,i), D2) eq true then
			return ff_m ! 0;
		end if;
	end for;
	
	if is_equal(D1, D2: add_alg := add_alg) then
		return ff_m ! 0;
	end if;
	
	mult_factor := 1;
	if IsDisjoint(Set(D1_zeroes), Set(D2_zeroes)) eq false then
		for i in [1..m] do
			D1_prime := Multiply(D1, C, i);
			D1_zeroes := ideal_to_divisor(D1_prime, C);
			mult_factor := i;
			if IsDisjoint(Set(D1_zeroes), Set(D2_zeroes)) then
				D1 := D1_prime;
				phi := [];
				break;
			end if;
		end for;
	end if;
	P := get_random_picard_point(C, BaseRing(Parent(Generators(D1)[1])));
	if phi eq [] then
		phi := jPower_with_function(D1, m, C: add_alg := add_alg);
	end if;
	if psi eq [] then
		psi := jPower_with_function(D2, m, C: add_alg := add_alg);
	end if;
	if D1_zeroes eq [] then
		D1_zeroes := ideal_to_divisor(D1, C);
	end if;
	g_poly_ring := Parent(phi[1][1]);
	g_x := Name(g_poly_ring, 1);
	g_y := Name(g_poly_ring, 2);
	phi[1][1] := phi[1][1]*(g_x^(#D1_zeroes*m));
	phi[1][2] := phi[1][2]*(g_y^(#D1_zeroes*m));
	if div_at_infty eq [] then
		D1_zeroes, D1_poles := move_divisor_away_from_infty(D1, C);
	else
		D1_zeroes := D1_zeroes cat div_at_infty[1];
		D1_poles := div_at_infty[2];
	end if;
	phi_poles := [];
	phi_zeroes := [];
	for i in [1..m] do
		phi_poles := phi_poles cat D1_poles;
		phi_zeroes := phi_zeroes cat D1_zeroes;
	end for;
	if D2_zeroes eq [] then
		D2_zeroes := ideal_to_divisor(D2, C);
	end if;
	D2_poles := [];
	phi_at_infty := evaluate_at_infinity(phi_zeroes, phi_poles, phi, C);
	h_m_value := (evaluate_function(D1_zeroes, D1_poles, psi, C: add_alg := add_alg)*phi_at_infty^#D2_zeroes/(evaluate_function(D2_zeroes, D2_poles, phi, C: add_alg := add_alg)));
	if h_m_value eq 1 then
		return ff_m ! 0;
	end if;
	ff_q := Parent(h_m_value);
	zeta_m := ff_q ! RootOfUnity(m, PrimeField(BaseRing(Parent(Generators(D1)[1]))));
	zeta_k := ff_q ! h_m_value;
	k := 1;
	while true do
		if zeta_m^k eq zeta_k then
			return (ff_m ! k)/mult_factor;
		end if;
		if k gt m+1 then
			error Error("Not a root of unity");
			return 0;
		end if;
		k +:= 1;
	end while;	
end intrinsic;

// Check if div(D1) and div(D2) have disjoint sets of zeroes
intrinsic is_disjoint(D1::RngMPol, D2::RngMPol, C::Crv : add_alg := 1) -> BoolElt
{}
	D1 := ideal_to_divisor(D1, C);
	D2 := ideal_to_divisor(D2, C);
	
	return IsDisjoint(Set(D1), Set(D2));
end intrinsic;

intrinsic move_divisor(D1::RngMPol, D2::RngMPol, C::Crv : add_alg := 1) -> RngMPol
{}
	R := Parent(Generators(D1)[1]);
	f := poly_from_curve(C, R: add_alg := add_alg);
	P := ideal< R | f >;
	D_inv := jReduce(D1, P, R);
	Groebner(D_inv);
	for g in Generators(D_inv) do
		J := ideal<R | g> + P;
		Groebner(J);
		J := IdealQuotient(J,D_inv) + P;
		Groebner(J);
		if is_disjoint(J, D2, C: add_alg := add_alg) eq true then
			return J;
		end if;
	end for;
	
	print "Failed to move divisor";
	return D1;
end intrinsic;

intrinsic make_disjoint(D1::RngMPol, D2::RngMPol, C::Crv : add_alg := 1) -> RngMPol
{}
	D1 := move_divisor(D1, D2, C: add_alg := add_alg);
	return D1;
end intrinsic;

intrinsic is_disjoint_list(basis_l::SeqEnum, C::Crv : add_alg := 1) -> BoolElt
{}
	for i in [1..#basis_l] do
		for j in [1..#basis_l] do
			if i lt j then
				if is_disjoint(basis_l[i], basis_l[j], C: add_alg := add_alg) eq false then
					return false;
				end if;
			end if;
		end for;
	end for;
	return true;
end intrinsic;

intrinsic make_disjoint_list(basis_l::SeqEnum, C::Crv : add_alg := 1) -> SeqEnum
{}
	for i in [1..#basis_l] do
		for j in [1..#basis_l] do
			if i lt j then
				if is_disjoint(basis_l[i], basis_l[j], C: add_alg := add_alg) eq false then
					basis_l[i] := make_disjoint(basis_l[i], basis_l[j], C: add_alg := add_alg);
				end if;
			end if;
		end for;
	end for;
	return basis_l;
end intrinsic;

// Computes pairing matrix for weil pairing
intrinsic compute_pairing_matrix(basis_l::SeqEnum, l::RngIntElt, C::Crv : add_alg := 1, basis_l_divs := []) -> AlgMatElt
{}
	ff_l := FiniteField(l);
	A := ZeroMatrix(ff_l, #basis_l, #basis_l);
	pairing_functions := [];
	for i in [1..#basis_l] do
		Append(~pairing_functions, jPower_with_function(basis_l[i], l, C: add_alg := add_alg));
	end for;
	
	Di_zeroes := [];
	for i in [1..#basis_l] do
		if #basis_l_divs ge i then
			Append(~Di_zeroes, basis_l_divs[i]);
		else
			Append(~Di_zeroes, ideal_to_divisor(basis_l[i], C));
		end if;
	end for;

	g_poly_ring := 	Parent(Generators(basis_l[1])[1]);
	g_x := Name(g_poly_ring, 1);
	g_y := Name(g_poly_ring, 2);
	zeroes, poles := function_to_divisor([g_x^3, g_y^3], C);

	for i in [1..#basis_l] do
		for j in [1..#basis_l] do
			if i gt j then
				continue;
			end if;
			if i eq j then
				A[i, j] := 0;
			else
				A[i, j] := weil_pairing(basis_l[i], basis_l[j], l, C: add_alg := add_alg, phi := pairing_functions[i], psi := pairing_functions[j], D1_zeroes := Di_zeroes[i], D2_zeroes := Di_zeroes[j], div_at_infty := [zeroes, poles]);
				A[j, i] := -A[i,j];
			end if;
		end for;
	end for;
	return A;
end intrinsic;

intrinsic poly_from_curve(C::Crv, g_poly_ring::RngMPol : add_alg := add_alg) -> RngMPolElt
{}
	g_x := Name(g_poly_ring,1);
	g_y := Name(g_poly_ring,2);
	ff_q := CoefficientRing(g_poly_ring);
	f_coeffs := coefficients_of_picard_curve(C, ff_q);
	f := 0;
	for i in [1..#f_coeffs] do
		f +:= f_coeffs[i]*g_x^(i-1);
	end for;
	f := g_y^3 - f;
	return f;
end intrinsic;

intrinsic picard_add(D1::RngMPol, D2::RngMPol, C::Crv : add_alg := 1) -> RngMPol, SeqEnum
{}

	if add_alg eq 1 then
		f := 0;
		g_poly_ring := Parent(Generators(D1)[1]);
		g_x := Name(g_poly_ring,1);
		g_y := Name(g_poly_ring,2);
		ff_q := CoefficientRing(g_poly_ring);

		// Force D2 to belong to same ring as D1
		R2 := Parent(Generators(D2)[1]);
		x2 := Name(R2,1);
		y2 := Name(R2,2);
		assert CoefficientRing(g_poly_ring ) eq CoefficientRing(Parent(Generators(D2)[1]));
		D2_gens := [];
		for gen in Generators(D2) do
			new_gen := 0;
			for i in [0..(#Coefficients(gen,x2)-1)] do
				for j in [0..(#Coefficients(gen,y2)-1)] do
					new_gen +:= (ff_q ! MonomialCoefficient(gen,x2^i*y2^j))*g_x^i*g_y^j;
				end for;
			end for;
			Append(~D2_gens, new_gen);			
		end for;
		D2 := ideal<g_poly_ring|D2_gens>;


		f_coeffs := coefficients_of_picard_curve(C, ff_q);
		for i in [1..#f_coeffs] do
			f +:= f_coeffs[i]*g_x^(i-1);
		end for;
		f := g_y^3 - f;
		P := ideal< g_poly_ring | f >;
		D, n_d := jSum(D1, D2, P, g_poly_ring);
		return D, n_d;
	end if;


	D1_tuple := divisor_poly_to_tuple(D1[1], D1[2]);
	D2_tuple := divisor_poly_to_tuple(D2[1], D2[2]);

	for elem in D1_tuple do
		if elem ne 0 then
			ff_q := Parent(elem);
			break;
		end if;
	end for;

	f_coeffs := coefficients_of_picard_curve(C, ff_q);

	f0 := f_coeffs[1];
	f1 := f_coeffs[2];
	f2 := f_coeffs[3];

	h0 := 0;
	h1 := 0;
	h2 := 0;
	h3 := 0;

	if is_zero_jac(D1, C: add_alg := add_alg) then
		return D2;
	end if;
	if is_zero_jac(D2, C: add_alg := add_alg) then
		return D1;
	end if;

	if D1[1] eq D2[1] and D1[2] eq D2[2] then
		Div3 := doubling(D1_tuple, f0, f1, f2, h0, h1, h2, h3);
	else
		Div3 := addition(D1_tuple, D2_tuple, f0, f1, f2, h0, h1, h2, h3);
	end if;

	u,v := tuple_to_mumford_rep(Div3);

	return [u,v], 0;
end intrinsic;

intrinsic is_zero_jac(D::RngMPol, C::Crv: add_alg := 1, L := IntegerRing()) -> BoolElt
{}
	if add_alg eq 1 then
		if Generators(D)[1] eq 1 then
			return true;
		end if;

		return false;
	end if;

	if D[1] eq 0 and D[2] eq 0 then
		return true;
	end if;
	return false;
end intrinsic;


// Assumes m positive
intrinsic is_zero_jac_multi(D::RngMPol, C::Crv, m::RngIntElt : add_alg :=1) -> BoolElt
{}

	if add_alg eq 1 then
		D0 := Multiply(D,C,m: add_alg:=add_alg);

		return is_zero_jac(D0,C: add_alg := add_alg);
	end if;

	u := D[1];
	v := D[2];
	if u eq 0 and v eq 0 then
		return true;
	end if;
	try
		D1 := picard_multiply([u,v], C, m+1: add_alg := add_alg);
		if D1[1] eq u and D1[2] eq v then
			return true;
		end if;
		return false;
	catch e // Assume that the error is because D1 is m+1 torsion
		try
			ff_q := CoefficientRing(Parent(u));
			g_poly_ring<g_x,g_y> := PolynomialRing(ff_q,2,"weight", [3,4, 0,1]);	
			u_temp := g_poly_ring ! 0;
			v_temp := g_poly_ring ! 0; 
			for i in [1..(Degree(u)+1)] do
				u_temp +:= Coefficients(u)[i]*g_x^(i-1);
			end for;
			for i in [1..(Degree(v)+1)] do
				v_temp +:= Coefficients(v)[i]*g_x^(i-1);
			end for;
			D := ideal< g_poly_ring | u_temp, g_y - v_temp>;


			return is_zero_jac_multi(D, C, m: add_alg := 1);
		catch e2
			print "Is Zero Jac Multi Error";
			print e2;
			error e`Object;
		end try;
	end try;
	
end intrinsic;


intrinsic picard_multiply(D0::RngMPol, C::Crv, m::RngIntElt : add_alg := 1) -> RngMPol
{}
	if m lt 0 then
		D0 := picard_inverse(D0, C: add_alg := add_alg);
		m := -m;
	end if;

	if add_alg eq 1 then
		g_poly_ring := Parent(Generators(D0)[1]);
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
		D := jPower(m, D0, P, g_poly_ring);
		return D;
	end if;

	if m eq 0 then
		return [0,0];
	end if;

	if m eq 1 then
		return D0;
	end if;

	D0 := divisor_poly_to_tuple(D0[1], D0[2]);

	for elem in D0 do
		if elem ne 0 then
			ff_q := Parent(elem);
			break;
		end if;
	end for;

	f_coeffs := coefficients_of_picard_curve(C, ff_q);

	f0 := f_coeffs[1];
	f1 := f_coeffs[2];
	f2 := f_coeffs[3];

	h0 := 0;
	h1 := 0;
	h2 := 0;
	h3 := 0;

	D1 := Multi(D0, h0,h1,h2,h3,f0,f1,f2, m);

	u,v := tuple_to_mumford_rep(D1);

	return [u,v];
end intrinsic;

intrinsic Multiply(D0::RngMPol, C::Crv, m::RngIntElt : add_alg :=1) -> RngMPol
{}
	D1 := picard_multiply(D0, C, m: add_alg := add_alg);

	return D1;
end intrinsic;

// !! Only for Picard Curves !!
intrinsic tuple_to_mumford_rep(D::SeqEnum) -> RngUPolElt, RngUPolElt
{}
	for elem in D do
		if elem ne 0 then
			ff_q := Parent(D[1]);
			break;
		end if;
	end for;
	R<x> := PolynomialRing(ff_q);
	u := D[1] + D[2]*x + D[3]*x^2 + x^3;
	v := D[4] + D[5]*x + D[6]*x^2;
	return u, v;
end intrinsic;

intrinsic zero_jac(C::Crv, ff_q::FldFin : add_alg := 1) -> RngMPol
{}
	if add_alg eq 1 then
		g_poly_ring<g_x,g_y> := PolynomialRing(ff_q,2,"weight", [3,4, 0,1]);
		return ideal<g_poly_ring|1>;
	end if;
end intrinsic;
