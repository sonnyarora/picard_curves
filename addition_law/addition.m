forward addition;

function addition (D1, D2, f0, f1, f2, h0, h1, h2, h3)

u10 := D1[1];
u11 := D1[2];
u12 := D1[3];

v10 := D1[4];
v11 := D1[5];
v12 := D1[6];


u20 := D2[1];
u21 := D2[2];
u22 := D2[3];

v20 := D2[4];
v21 := D2[5];
v22 := D2[6];


// step 1

//  compute the inverse t1 of v1-v2 modulo u2
//  13M + 2SQ

t10,t11,t12,res1 := modular_inverse_3n_2 (u20, u21, u22, v10-v20, v11-v21, v12-v22);

//  compute c:=(u1-u2)t1
//  5M

c0,c1,c2,c3,c4 := toom_cook_2_2 (u10-u20,u11-u21,u12-u22,t10,t11,t12);

// compute the remainder r of c by u2
//  4M
//Vorsicht: mit den Zeichen r0,r1,r2: die habe ich aus den anderen Implem. so uebernommen ...

r2,r1,r0 := remainder_4_3n (c0, c1, c2, c3, c4, u20, u21, u22);

// Solve the linear equation

//  5M + 1SQ

tmp1 := res1 * (v12+v22);
tmp2 := v12^2;
tmp3 := r0 * tmp2;
tmp4 := r1 * tmp2;
tmp5 := tmp3 * u22;
gamma1_p :=tmp1-(tmp4 - tmp5);
Gamma1 := gamma1_p * res1;

//  compute the part s of w:= res1 r0 y^2 + s y + t with interpolation by 0 and 1:
//  8M

tmp6  := res1 * r0;
tmp7  := r0 * tmp3;
tmp8  := r2 * gamma1_p;
tmp9  := tmp7 * u20;
tmp10 := tmp6 * (v10 + v20);
sval0 := tmp8 - tmp9 - tmp10;

rval1  := r0 + r1 + r2;
u2val1 := 1 + u22 + u21 + u20;
v1val1 := v12 + v11 + v10;
v2val1 := v22 + v21 + v20;

tmp11 := rval1 * (tmp3 + gamma1_p);
tmp12 := tmp7 * u2val1;
tmp13 := tmp6 * (v1val1 + v2val1);

sval1  := tmp11 - tmp12 - tmp13;

// s = s0 + s1 x
s0 := sval0;
s1 := sval1 - sval0;

// Compute Coeff(w,x,3);
// 4M

tmp14 := mulconst(tmp6 * v11, 2);
tmp15 := v12 * (s1 + tmp14);
tmp16 := tmp6 * tmp2;
tmp17 := u12 * tmp16;
coeff_w_x_3 := Gamma1 + tmp17 - tmp15;


// compute simultaneous inverse, such that the computing of the reultant should be easy and monic ...
// Cost :  if h3 eq 0 ===> 2M + 1SQ + 1I
//         if h3 ne 0 ===> 8M + 2SQ + 1I

tmp18    := tmp6 * coeff_w_x_3;
tmp19    := tmp6^2;


if h3 eq 0 then
   inv      := invert(tmp18);
   coeffwx3_res1r0_m1 := inv;
   tmp20    := inv * coeff_w_x_3;
   res1r0m1 := tmp20;
else
   tmp20    := h3 * tmp19;
   tmp21    := h3 * ( -mulconst(tmp18,2) + tmp20);
   tmp22    := coeff_w_x_3^2;
   B        := tmp22 + tmp21;
   tmp23    := tmp18 * B;
   inv      := invert(tmp23);
   tmp24    := B * inv;
   coeffwx3_res1r0_m1 := tmp24;
   tmp25    := coeff_w_x_3 * coeffwx3_res1r0_m1;
   res1r0m1 := tmp25 ;
   tmp26    := inv * tmp18;

   Bm1      := tmp26;
   tmp27    := tmp22 * Bm1;
   Am1      := tmp27 ;
   // we use Am1 later, as we need to make the resltant monic.
end if;

//  Compute sy := sy1 x + sy 0 ( = s /( res1 r0))
//  2M

tmp28 := s0 * res1r0m1 ;
tmp29 := s1 * res1r0m1  ;
sy0 := tmp28;
sy1 := tmp29;

// Compute ty := u1 ( v12^2 x + gamma1) -v1 (v1 +sy) and tx := ty (res1 r0) ^2 ( res1 r0 coeff(w,x,3) )^(-1)

// 12M
tmp30 := Gamma1 * res1r0m1;
gamma1 :=  tmp30;
tmp31 := u10 * gamma1;
tmp32 := v10 * (v10 + sy0);
tmp33 := (1+ u12 + u11 + u10) * (tmp2 + gamma1);
tmp34 := (v12 + v11 + v10) * (v12 + v11 + v10 + sy1 + sy0);
tmp35 := (-1 + u12 - u11 + u10) * (- tmp2 + gamma1);
tmp36 := (v12 - v11 + v10) * (v12 - v11 + v10 - sy1 + sy0);
tmp37 := coeff_w_x_3 * res1r0m1;

tyval0   := tmp31 - tmp32;
tyval1   := tmp33 - tmp34;
tyvalm1  := tmp35 - tmp36;
tyvalinf := tmp37;

// for the following operation, no multiplication are necessary...
ty0, ty1, ty2, ty3 := interpolate(tyval0, tyval1, tyvalm1, tyvalinf);

tmp38 := tmp19 * coeffwx3_res1r0_m1;
tmp39 := ty0 * tmp38;
tmp40 := ty1 * tmp38;
tmp41 := ty2 * tmp38;

tx0 := tmp39;
tx1 := tmp40;
tx2 := tmp41;

// Step 2:

// first coeff von tx^3 := x^9 + tx3_8 * x^8 + tx3_7 * x^7 + tx3_6 * x^6
// 1SQ + 1M

tmp42 := tx2^2;
tmp43 := tx2 * ( mulconst ( mulconst ( tx1,2 ) , 3 ) + tmp42 );
tx3_8 := mulconst (tx2,3);
tx3_7 := mulconst ( tx1 + tmp42, 3 );
tx3_6 := tmp43 + mulconst (tx0,3);

// Berechnung von sy^2 := sy2_0 + sy2_1 * x + sy2_2 *x^2
//  3SQ

tmp44 := sy1^2;
tmp45 := (sy1 + sy0)^2;
tmp46 := sy0^2;


sy2_0 := tmp46;
sy2_1 := (tmp45 - tmp44 - tmp46);
sy2_2 := tmp44;

// Computing of sy * ty := syty4 * x^4 + syty3 * x^3 + syty2 * x^2 + syty1 * x + syty0
// 5M
syty0, syty1, syty2, syty3, syty4 := toom_cook_1_3 (sy0,sy1,ty0,ty1,ty2,ty3);

// first coeff von sy^3 := sy3_3*x^3 + sy3_2 * x^2
// 2M

tmp47 := sy1 * sy2_2;
tmp48 := mulconst( sy2_2 * sy0, 3);
sy3_3 := tmp47;
sy3_2 := tmp48;


//  Computing of H1:= H18 * x^8  + H17 * x^7 + H16 * x^6;
//  1M

tmp49 := (1 - mulconst( syty4 ,3 )) * f2;

H18 := 1 - mulconst( syty4 ,3 ) ;
H17 := sy3_3 - mulconst( syty3 ,3 );
H16 := f2 + sy3_2 - mulconst( syty2 ,3 ) + tmp49;

// Computing H2:

if ( h0 eq 0 and h1 eq 0 and h2 eq 0 and h3 eq 0) then
// Picard curves case:

   H23:=0;H24:=0;H25:=0;H26:=0;H27:=0;H28:=0;H29:=0;
elif ( h1 eq 0 and h2 eq 0 and h3 eq 0) then
// h is a constant (h3=h2=h1=0 and h0 ne 9)
   // 1M + 1SQ
   tmp50 := - mulconst( ty3^2 , 2 );
   tmp51 := h0 * tmp50;
   H23:=0;H24:=0;H25:=0;
   H26   := tmp51;
   H27:=0; H28:=0;H29:=0;
elif ( h2 eq 0 and h3 eq 0) then
// h is linear
   // 6M
   P0,P1,P2 := toom_cook_1_1 (ty2, ty3, sy2_2 - mulconst( ty2, 2 ), - mulconst( ty3, 2 ));
   H25,H26,H27 := toom_cook_1_1 (h0, h1, P1 + sy1, P2);
   H23:=0;H24:=0;H28:=0;H29:=0;
elif ( h3 eq 0) then
// h is quadratic
   // 10M
   P0,P1,P2,P3,P4 := toom_cook_2_2 (ty1, ty2, ty3, sy2_1 - mulconst( ty1, 2 ) + h1, sy2_2 - mulconst( ty2, 2 ) + h2, - mulconst( ty3, 2 ));
   H24,H25,H26,H27,H28 := toom_cook_2_2 (h0, h1, h2,  P2 +sy0,  P3 +sy1, P4);
   H29:=0;
else
// h is cubic
   // 15M
   P0,P1,P2,P3,P4,P5,P6 := toom_cook_3_3 (ty0, ty1, ty2, ty3, sy2_0 - 2* ty0 + h0, sy2_1 - 2* ty1 + h1, sy2_2 - 2* ty2 + h2, - 2 * ty3 + h3);
   tmp52 := f2 * sy1;
   H23,H24,H25,H26,H27,H28,H29 := toom_cook_3_3 (h0, h1, h2, h3, P3 + tmp52 , P4 + sy0,  P5 + sy1, P6);
end if;


// Berechnung der Resultante:
// resWC:= (k1^3 *( H1 + H2 ) + tx^3) * Am1 , notice that Am1 is equal to 1 if deg(h) < 3!!!


//   1SQ  + 4M
k1    := tmp38;
tmp53 := k1^2;
tmp54 := k1 * tmp53;

tmp55 := tmp54 *( H16 + H26 );
tmp56 := tmp54 *( H17 + H27 );
tmp57 := tmp54 *( H18 + H28 );

if h3 eq 0 then
   ReswC6 := tmp55 + tx3_6;
   ReswC7 := tmp56 + tx3_7;
   ReswC8 := tmp57 + tx3_8;
   Am1:=1;
else
   // 3M
   tmp58 := (tmp55 + tx3_6) * Am1;
   tmp59 := (tmp56 + tx3_7) * Am1;
   tmp60 := (tmp57 + tx3_8) * Am1;

   ReswC6 := tmp58;
   ReswC7 := tmp59;
   ReswC8 := tmp60;
end if;

// Computing the first term of U:=u1*u2 = x^6 + U5*x^5 + U4*x^4 + U3 * x^3 + ....
// 3M
tmp61 := u12 * u22;
tmp62 := u12 * u21;
tmp63 := u11 * u22;

U5 := u12 + u22;
U4 := u21 + u11 + tmp61;
U3 := u20 + u10 + tmp62 + tmp63;

// 3M
Um0, Um1, Um2 := quotient_6n_3n (ReswC6, ReswC7, ReswC8, U3, U4, U5);

//  16M + 2SQ
alpha10, alpha11, alpha12, res2 := modular_inverse_3n_3 (Um0, Um1, Um2, ty0 - sy2_0 - h0, ty1 - sy2_1 - h1, ty2 - sy2_2 - h2, ty3 - h3);

// 4M
Rem10,Rem11,Rem12:= remainder_4_3n (syty0 - f0 , syty1 -f1, syty2 - f2, syty3, syty4 - 1 , Um0, Um1, Um2);

//  5M
Rem20,Rem21,Rem22,Rem23,Rem24:= toom_cook_2_2 (Rem10,Rem11,Rem12,alpha10,alpha11,alpha12);

// 4M
fauxV12_0, fauxV12_1, fauxV12_2 := remainder_4_3n (Rem20 , Rem21, Rem22, Rem23, Rem24 , Um0, Um1, Um2);

// 5M + 1I
tmp64   := res2 *fauxV12_2;
inv2    := invert(tmp64);
tmp65   := inv2*fauxV12_2;
invres2 := tmp65;


vD1D2_0 := invres2 * fauxV12_0;
vD1D2_1 := invres2 * fauxV12_1;
vD1D2_2 := invres2 * fauxV12_2;

// uD1D2:=((inv2*res2^2*vD1D2)^3+(inv2*res2^2)^3*UnivariatePolynomial(f4)-(inv2*res2^2)^3*h1*vD1D2^2+(inv2*res2^2)^3*h2*vD1D2) div u_D1D2;
//  5M + 3SQ

tmp66 := res2^2;
tmp67 := inv2 * tmp66;
tmp68 := tmp67^2;
tmp69 := tmp68 * tmp67;
tmp70 := tmp67 * vD1D2_1 ;
tmp71 := tmp70^2 ;
tmp72 := tmp67 * vD1D2_0 ;
tmp73 := tmp70 * (tmp71 + mulconst ( mulconst ( tmp72 , 2), 3)) ;

if ( h0 eq 0 and h1 eq 0 and h2 eq 0 and h3 eq 0) then
// Picard curves case:

   tot5 := mulconst( tmp70, 3);
   tot4 := mulconst(tmp72 + tmp71, 3) - tmp69;
   tot3 := tmp73;

elif ( h1 eq 0 and h2 eq 0 and h3 eq 0) then
// h is a constant (h3=h2=h1=0 and h0 ne 9)

   tot5 := mulconst(tmp70, 3);
   tot4 := mulconst(tmp72+ tmp71, 3) - tmp69;
   tot3 := tmp73;

elif ( h2 eq 0 and h3 eq 0) then
// h is linear
   //   2M
   tmp74 := h1 * vD1D2_2;
   tmp75 := tmp69 * tmp74; // coeff bei x^3

   tot5 := mulconst( tmp70, 3);
   tot4 := mulconst(tmp72 + tmp71, 3) - tmp69;
   tot3 := tmp73 + tmp75;

elif ( h3 eq 0) then
// h is quadratic
   // 5M
   tmp74, tmp75, tmp76 := toom_cook_1_1 (vD1D2_1,vD1D2_2,h1,h2);
   tmp77 := tmp69 * tmp75; // coeff bei x^3
   tmp78 := tmp69 * tmp76; // coeff bei x^4

   tot5 := mulconst( tmp70, 3);
   tot4 := mulconst( tmp72 + tmp71, 3) - tmp69 + tmp78;
   tot3 := tmp73 + tmp77;

else
// h is cubic
   // 8M
   tmp74, tmp75, tmp76, tmp77, tmp78 := toom_cook_2_2 (vD1D2_0, vD1D2_1, vD1D2_2 , h1,h2, h3 );
   tmp79 := tmp69 * tmp76; // coeff bei x^3
   tmp80 := tmp69 * tmp77; // coeff bei x^4
   tmp81 := tmp69 * tmp78; // coeff bei x^5

   tot5 := mulconst( tmp70, 3) + tmp81;
   tot4 := mulconst( tmp72+ tmp71, 3) - tmp69 +tmp80;
   tot3 := tmp73 + tmp79;

end if;

// 3M
UD1D2_0, UD1D2_1, UD1D2_2 := quotient_6n_3n (tot3, tot4, tot5, Um0, Um1, Um2);

return [UD1D2_0, UD1D2_1, UD1D2_2, vD1D2_0, vD1D2_1, vD1D2_2];

end function;


function doubling (D1, f0, f1, f2, h0, h1, h2, h3)

u10 := D1[1];
u11 := D1[2];
u12 := D1[3];

v10 := D1[4];
v11 := D1[5];
v12 := D1[6];

// step 1
//  compute v1^3 + v1 *h - f =  v1 * ( v1^2 + h ) - f

// First compute v1^2

v1val1 := v12 + v11 + v10;
v1valm1 := v12 - v11 + v10;
v1val2 := mulconst (v12, 4) + mulconst (v11, 2) + v10;

// 5SQ
v2_0, v2_1, v2_2, v2_3, v2_4 := toom_cook_square_2 (v10,v11,v12);

// Compute the 4 highest coefficients of
// v1 * (v1^2 + h) - f into a variable b.
// For this S (4, 3; 4), perform first Toom-Cook on the 3 highest
// coefficients.

// 6M
b1,b2,b3,b4,b5,b6 :=toom_cook_2_3 (v10, v11, v12, v2_1 + h1, v2_2 + h2, v2_3 + h3, v2_4 );

// correct:

b4:=  b4 - 1;

// Perform an exact division by u1 to obtain w1.
// 6M

   w13 := b6;
   w12 := b5 - w13 * u12;
   w11 := b4 - w13 * u11 - w12 * u12;
   w10 := b3 - w13 * u10 - w12 * u11 - w11 * u12;

//  compute the inverse t1 of w1 modulo u1
//  with the Euclidian algorithm between c = w1 and u1
//  16M + 2SQ

t10,t11,t12,res1 := modular_inverse_3n_3 (u10, u11, u12, w10, w11, w12, w13);


//  compute Remainder ( 3 v1^2 + h, u1)
//  4M

Rem1_0 ,Rem1_1, Rem1_2 := remainder_4_3n ( mulconst( v2_0,3) + h0, mulconst( v2_1, 3) + h1 , mulconst( v2_2, 3) + h2, mulconst( v2_3, 3) + h3, mulconst( v2_4,3), u10, u11, u12);

// 5M
c0,c1,c2,c3,c4 := toom_cook_2_2 (Rem1_0, Rem1_1 , Rem1_2 , t10 , t11 , t12);

// compute the remainder r of c by u1
//  4M
//Vorsicht: mit den Zeichen r0,r1,r2: die habe ich aus den anderen Implem. so uebernommen ...

r2,r1,r0 := remainder_4_3n (c0, c1, c2, c3, c4, u10, u11, u12);


// Solve the linear equation

//  5M

tmp1 := mulconst( res1 * v12, 2);
tmp2 := v2_4;
tmp3 := r0 * tmp2;
tmp4 := r1 * tmp2;
tmp5 := tmp3 * u12;
gamma1_p :=tmp1-(tmp4 - tmp5);
Gamma1 := gamma1_p * res1;

//  compute the part s of w:= res1 r0 y^2 +s y + t with interpolation by 0 and 1:
//  8M

tmp6  := res1 * r0;
tmp7  := r0 * tmp3;
tmp8  := r2 * gamma1_p;
tmp9  := tmp7 * u10;
tmp10 := mulconst( tmp6 * v10, 2);
sval0 := tmp8 - tmp9 - tmp10;

rval1  := r0 + r1 + r2;
u1val1 := 1 + u12 + u11 + u10;
v1val1 := v12 + v11 + v10;

tmp11 := rval1 * (tmp3 + gamma1_p);
tmp12 := tmp7 * u1val1;
tmp13 := mulconst( tmp6 * v1val1, 2);

sval1  := tmp11 - tmp12 - tmp13;

// s = s0 + s1 x
s0 := sval0;
s1 := sval1 - sval0;

// Compute Coeff(w,x,3);
// 4M

tmp14 := mulconst(tmp6 * v11, 2);
tmp15 := v12 * (s1 + tmp14);
tmp16 := tmp6 * tmp2;
tmp17 := u12 * tmp16;
coeff_w_x_3 := Gamma1 + tmp17 - tmp15;


// compute simultaneous inverse, such that the computing of the reultant should be easy and monic ...
// Cost :  if h3 eq 0 ===> 2M + 1SQ + 1I
//         if h3 ne 0 ===> 8M + 2SQ + 1I

tmp18    := tmp6 * coeff_w_x_3;
tmp19    := tmp6^2;

if h3 eq 0 then
   inv      := invert(tmp18);
   coeffwx3_res1r0_m1 := inv;
   tmp20    := inv * coeff_w_x_3;
   res1r0m1 := tmp20;
else
   tmp20    := h3 * tmp19;
   tmp21    := h3 * ( -mulconst(tmp18,2) + tmp20);
   tmp22    := coeff_w_x_3^2;
   B        := tmp22 + tmp21;
   tmp23    := tmp18 * B;
   inv      := invert(tmp23);
   tmp24    := B * inv;
   coeffwx3_res1r0_m1 := tmp24;
   tmp25    := coeff_w_x_3 * coeffwx3_res1r0_m1;
   res1r0m1 := tmp25 ;
   tmp26    := inv * tmp18;

   Bm1      := tmp26;
   tmp27    := tmp22 * Bm1;
   Am1      := tmp27 ;
   // we use Am1 later, as we need to make the resultant monic.
end if;

//  Compute sy := sy1 x + sy 0 ( = s /( res1 r0))
//  2M

tmp28 := s0 * res1r0m1 ;
tmp29 := s1 * res1r0m1  ;
sy0 := tmp28;
sy1 := tmp29;

// Compute ty := u1 ( v12^2 x + gamma1) -v1 (v1 +sy) and tx := ty (res1 r0) ^2 ( res1 r0 coeff(w,x,3) )^(-1)
// 12M

tmp30 := Gamma1 * res1r0m1;
gamma1 :=  tmp30;
tmp31 := u10 * gamma1;
tmp32 := v10 * (v10 + sy0);
tmp33 := (1+ u12 + u11 + u10) * (tmp2 + gamma1);
tmp34 := (v12 + v11 + v10) * (v12 + v11 + v10 + sy1 + sy0);
tmp35 := (-1 + u12 - u11 + u10) * (- tmp2 + gamma1);
tmp36 := (v12 - v11 + v10) * (v12 - v11 + v10 - sy1 + sy0);
tmp37 := coeff_w_x_3 * res1r0m1;

tyval0   := tmp31 - tmp32;
tyval1   := tmp33 - tmp34;
tyvalm1  := tmp35 - tmp36;
tyvalinf := tmp37;

// for the following operation, no multiplication are necessary...

ty0, ty1, ty2, ty3 := interpolate(tyval0, tyval1, tyvalm1, tyvalinf);


tmp38 := tmp19 * coeffwx3_res1r0_m1;
tmp39 := ty0 * tmp38;
tmp40 := ty1 * tmp38;
tmp41 := ty2 * tmp38;

tx0 := tmp39;
tx1 := tmp40;
tx2 := tmp41;

// Step 2:

// first coeff von tx^3 := x^9 + tx3_8 * x^8 + tx3_7 * x^7 + tx3_6 * x^6
// 1SQ + 1M

tmp42 := tx2^2;
tmp43 := tx2 * ( mulconst ( mulconst ( tx1,2 ) , 3 ) + tmp42 );
tx3_8 := mulconst (tx2,3);
tx3_7 := mulconst ( tx1 + tmp42, 3 );
tx3_6 := tmp43 + mulconst (tx0,3);


// Berechnung von sy^2 := sy2_0 + sy2_1 * x + sy2_2 *x^2
//  3SQ

tmp44 := sy1^2;
tmp45 := (sy1 + sy0)^2;
tmp46 := sy0^2;


sy2_0 := tmp46;
sy2_1 := (tmp45 - tmp44 - tmp46);
sy2_2 := tmp44;

// Computing of sy * ty := syty4 * x^4 + syty3 * x^3 + syty2 * x^2 + syty1 * x + syty0
// 5M
syty0, syty1, syty2, syty3, syty4 := toom_cook_1_3 (sy0,sy1,ty0,ty1,ty2,ty3);


// first coeff von sy^3 := sy3_3*x^3 + sy3_2 * x^2
// 2M

tmp47 := sy1 * sy2_2;
tmp48 := mulconst( sy2_2 * sy0, 3);
sy3_3 := tmp47;
sy3_2 := tmp48;


//  Computing of H1:= H18 * x^8  + H17 * x^7 + H16 * x^6;
//  1M

tmp49 := (1 - mulconst( syty4 ,3 )) * f2;

H18 := 1 - mulconst( syty4 ,3 ) ;
H17 := sy3_3 - mulconst( syty3 ,3 );
H16 := f2 + sy3_2 - mulconst( syty2 ,3 ) + tmp49;

// Computing H2:


if ( h0 eq 0 and h1 eq 0 and h2 eq 0 and h3 eq 0) then
// Picard curves case:

   H23:=0;H24:=0;H25:=0;H26:=0;H27:=0;H28:=0;H29:=0;
elif ( h1 eq 0 and h2 eq 0 and h3 eq 0) then
// h is a constant (h3=h2=h1=0 and h0 ne 9)
   // 1M + 1SQ
   tmp50 := - mulconst( ty3^2 , 2 );
   tmp51 := h0 * tmp50;
   H23:=0;H24:=0;H25:=0;
   H26   := tmp51;
   H27:=0; H28:=0;H29:=0;
elif ( h2 eq 0 and h3 eq 0) then
// h is linear
   // 6M
   P0,P1,P2 := toom_cook_1_1 (ty2, ty3, sy2_2 - mulconst( ty2, 2 ), - mulconst( ty3, 2 ));
   H25,H26,H27 := toom_cook_1_1 (h0, h1, P1 + sy1, P2);
   H23:=0;H24:=0;H28:=0;H29:=0;
elif ( h3 eq 0) then
// h is quadratic
   // 10M
   P0,P1,P2,P3,P4 := toom_cook_2_2 (ty1, ty2, ty3, sy2_1 - mulconst( ty1, 2 ) + h1, sy2_2 - mulconst( ty2, 2 ) + h2, - mulconst( ty3, 2 ));
   H24,H25,H26,H27,H28 := toom_cook_2_2 (h0, h1, h2,  P2 +sy0,  P3 +sy1, P4);
   H29:=0;
else
// h is cubic
   // 15M
   P0,P1,P2,P3,P4,P5,P6 := toom_cook_3_3 (ty0, ty1, ty2, ty3, sy2_0 - mulconst(ty0,2) + h0, sy2_1 - mulconst(ty1,2) + h1, sy2_2 - mulconst(ty2,2) + h2, - mulconst(ty3, 2) + h3);
   tmp52 := f2 * sy1;
   H23,H24,H25,H26,H27,H28,H29 := toom_cook_3_3 (h0, h1, h2, h3, P3 + tmp52 , P4 + sy0,  P5 + sy1, P6);
end if;

// Berechnung der Resultante:
// resWC:= (k1^3 *( H1 + H2 ) + tx^3) * Am1 , notice that Am1 is equal to 1 if deg(h) < 3!!!

//   4M + 1SQ

k1    := tmp38;
tmp53 := k1^2;
tmp54 := k1 * tmp53;

tmp55 := tmp54 *( H16 + H26 );
tmp56 := tmp54 *( H17 + H27 );
tmp57 := tmp54 *( H18 + H28 );

if h3 eq 0 then
   ReswC6 := tmp55 + tx3_6;
   ReswC7 := tmp56 + tx3_7;
   ReswC8 := tmp57 + tx3_8;
   Am1:=1;
else
   // 3M
   tmp58 := (tmp55 + tx3_6) * Am1;
   tmp59 := (tmp56 + tx3_7) * Am1;
   tmp60 := (tmp57 + tx3_8) * Am1;

   ReswC6 := tmp58;
   ReswC7 := tmp59;
   ReswC8 := tmp60;
end if;


// Computing the first term of U:=u1*u2 = x^6 + U5*x^5 + U4*x^4 + U3 * x^3 + ....

// 1M + 1SQ

tmp61 := u12^2;
tmp62 := u12 * u11;
tmp63 := tmp62;

U5 := mulconst(u12, 2);
U4 := mulconst(u11,2) + tmp61;
U3 := mulconst(u10,2) + tmp62 + tmp63;

// 3M
Um0, Um1, Um2 := quotient_6n_3n (ReswC6, ReswC7, ReswC8, U3, U4, U5);

// 16M + 2SQ
alpha10, alpha11, alpha12, res2 := modular_inverse_3n_3 (Um0, Um1, Um2, ty0 - sy2_0 - h0, ty1 - sy2_1 - h1, ty2 - sy2_2 - h2, ty3 - h3);

// 4M
Rem10,Rem11,Rem12:= remainder_4_3n (syty0 - f0 , syty1 -f1, syty2 - f2, syty3, syty4 - 1 , Um0, Um1, Um2);

// 5M
Rem20,Rem21,Rem22,Rem23,Rem24:= toom_cook_2_2 (Rem10,Rem11,Rem12,alpha10,alpha11,alpha12);

// 4M
fauxV12_0, fauxV12_1, fauxV12_2 := remainder_4_3n (Rem20 , Rem21, Rem22, Rem23, Rem24 , Um0, Um1, Um2);

// 5M + 1I

tmp64   := (res2 *fauxV12_2);
inv2    := invert(tmp64);
tmp65   := inv2*fauxV12_2;
invres2 := tmp65;


vD1D2_0 := invres2 * fauxV12_0;
vD1D2_1 := invres2 * fauxV12_1;
vD1D2_2 := invres2 * fauxV12_2;

// uD1D2:=((inv2*res2^2*vD1D2)^3+(inv2*res2^2)^3*UnivariatePolynomial(f4)-(inv2*res2^2)^3*h1*vD1D2^2+(inv2*res2^2)^3*h2*vD1D2) div u_D1D2;

//  5M + 3SQ

tmp66 := res2^2;
tmp67 := inv2*tmp66;
tmp68 := tmp67^2;
tmp69 := tmp68*tmp67;
tmp70 := tmp67 * vD1D2_1 ;
tmp71 := tmp70^2 ;
tmp72 := tmp67 * vD1D2_0 ;
tmp73 := tmp70 * (tmp71 + mulconst ( mulconst ( tmp72 , 2), 3)) ;

if ( h0 eq 0 and h1 eq 0 and h2 eq 0 and h3 eq 0) then
// Picard curves case:

   tot5 := mulconst( tmp70, 3);
   tot4 := mulconst(tmp72 + tmp71, 3) - tmp69;
   tot3 := tmp73;

elif ( h1 eq 0 and h2 eq 0 and h3 eq 0) then
// h is a constant (h3=h2=h1=0 and h0 ne 9)

   tot5 := mulconst(tmp70, 3);
   tot4 := mulconst(tmp72+ tmp71, 3) - tmp69;
   tot3 := tmp73;

elif ( h2 eq 0 and h3 eq 0) then
// h is linear
   // 2M
   tmp74 := h1 * vD1D2_2;
   tmp75 := tmp69 * tmp74; // coeff bei x^3

   tot5 := mulconst(tmp70,3);
   tot4 := mulconst(tmp72+ tmp71, 3) - tmp69;
   tot3 := tmp73 + tmp75;

elif ( h3 eq 0) then
// h is quadratic
   // 5M
   tmp74, tmp75, tmp76 := toom_cook_1_1 (vD1D2_1,vD1D2_2,h1,h2);
   tmp77 := tmp69 * tmp75; // coeff bei x^3
   tmp78 := tmp69 * tmp76; // coeff bei x^4

   tot5 := mulconst( tmp70, 3);
   tot4 := mulconst( tmp72+ tmp71, 3) - tmp69 + tmp78;
   tot3 := tmp73 + tmp77;

else
// h is cubic
   // 8M
   tmp74, tmp75, tmp76, tmp77, tmp78 := toom_cook_2_2 (vD1D2_0, vD1D2_1, vD1D2_2 , h1,h2, h3 );
   tmp79 := tmp69 * tmp76; // coeff bei x^3
   tmp80 := tmp69 * tmp77; // coeff bei x^4
   tmp81 := tmp69 * tmp78; // coeff bei x^5

   tot5 := mulconst( tmp70, 3) + tmp81;
   tot4 := mulconst( tmp72+ tmp71, 3) - tmp69 +tmp80;
   tot3 := tmp73 + tmp79;

end if;

// 3M
UD1D2_0, UD1D2_1, UD1D2_2 := quotient_6n_3n (tot3, tot4, tot5, Um0, Um1, Um2);

return [UD1D2_0, UD1D2_1, UD1D2_2, vD1D2_0, vD1D2_1, vD1D2_2];

end function;
