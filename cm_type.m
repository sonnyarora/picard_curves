
// From avisogenies package
intrinsic reflex_field(T::SeqEnum) -> FldNum, Map
{}
  K:=Domain(Universe(T));
  L:=Codomain(Universe(T));
  assert IsPrimitive(K.1);
  P:=[t(K.1) : t in T];
  Q:=[g : g in Automorphisms(L) | g(P[1]) in P]; // EMB // induced CM type on L
  R:={q^-1 : q in Q};
  S:=[g : g in Automorphisms(L) | {g*r : r in R} eq R]; // S is the fixator of the

  U, embd:=FixedField(L,S); assert IsPrimitive(U.1);          // primitive CM type inducing R

  return U, embd;
end intrinsic;

// Checks whether a field is CM. Adapted from avisogenies TotallyRealField
intrinsic is_cm(K::FldNum) -> BoolElt
{}
 	r,s:=Signature(K); 
	assert r eq 0; //Check that field is imaginary

	// Check that field has totally real subfield
	S:=[F[1] : F in Subfields(K) | Degree(F[1]) eq s and IsTotallyReal(F[1])];
	if Degree(K) eq 2 then
		Append(~S, Rationals()); // As Subfields doesn't return QQ as one of the subfields
	end if;
	if #S eq 1 then
		return true;
	end if;
	
	return false;
end intrinsic;


intrinsic get_all_cm_types_from_embds(embds::SeqEnum) -> SeqEnum
{}

	assert IsEven(#embds);

	if #embds ne 0 then

		types:= {};
		for i in [1..#embds] do
			embds_temp := embds;
			s := embds_temp[i];

			Remove(~embds_temp,i);

			// Remove complex conjugate from list
			for j in [1..#embds_temp] do
				if embds_temp[j] eq ComplexConjugate(s) then
					Remove(~embds_temp, j);
					break;
				end if;
			end for;


			T := get_all_cm_types_from_embds(embds_temp);

			if T ne {} then

				for type in T do
					Include(~types, Include(type,s));
					Include(~types, Include(type,ComplexConjugate(s)));
				end for;
				
			else
				types := {{s}, {ComplexConjugate(s)}};
			end if;

		end for;

		return types;
	end if;

	return {};
end intrinsic;


// Computes all possible CM types for the CM field K
intrinsic get_all_cm_types_from_field(K::FldNum) -> SeqEnum
{}
	assert IsPrimitive(K.1);
	assert is_cm(K);
	print "Before Splitting Field";
	L,l:=SplittingField(K);
	print "After Splitting Field";

	T := get_all_cm_types_from_embds(l);
	types := {};
	for type in T do
		Include(~types, [hom<K->L | t> : t in type]);
	end for;
	return types;
end intrinsic;

// Computes a possible CM type for the CM field
intrinsic get_random_cm_type(K::FldNum) -> SeqEnum
{}
	assert IsPrimitive(K.1);
	L,l:=SplittingField(K);
	T:={};
	g := IntegerRing() ! #l/2;
	while #l ne g do
		i := Random(1,#l);
		s := l[i];
		if not s in T and not s in {ComplexConjugate(t) : t in T} then 
			Include(~T,s);
			Remove(~l,i);
		end if;
	end while;
	return [hom<K->L | t> : t in T];
end intrinsic;

intrinsic is_primitive_type(T::SeqEnum) ->BoolElt
{}

	K:=Domain(Universe(T));
	L:=Codomain(Universe(T));
	assert IsPrimitive(K.1);
	P:=[t(K.1) : t in T];

	perms, _, maps := AutomorphismGroup(L);

	auts := {maps(g) : g in perms};
	Phi:={g : g in perms | maps(g)(P[1]) in P}; // EMB // induced CM type on L

	S:=[g : g in perms |  {phi : phi in Phi} eq {(g*phi) : phi in Phi}]; // S is the fixator of the

	H := FixedGroup(L, K);
	H_prime := sub<perms|S>;

	is_conj, _ := IsConjugate(perms, H, H_prime);

	return is_conj;

end intrinsic;

// Assumes the existence of a primitive CM-type
intrinsic get_primitive_cm_type(K::FldNum) -> SeqEnum
{}
	while true do
		Phi := get_random_cm_type(K);

		if is_primitive_type(Phi) eq true then
			return Phi;
		end if;
	end while;

	return 0;

end intrinsic;

intrinsic get_all_primitive_cm_types(K::FldNum) -> SeqEnum
{}
	types := get_all_cm_types_from_field(K);
	primitive_types := [];
	for type in types do
		if is_primitive_type(type) then
			Include(~primitive_types, type);
		end if;
	end for;
	return primitive_types;
end intrinsic;

intrinsic get_all_imprimitive_cm_types(K::FldNum) -> SeqEnum
{}
	types := get_all_cm_types_from_field(K);
	imprimitive_types := [];
	for type in types do
		if is_primitive_type(type) eq false then
			Include(~imprimitive_types, type);
		end if;
	end for;
	return imprimitive_types;
end intrinsic;
 
