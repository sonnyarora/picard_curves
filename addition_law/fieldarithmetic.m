

/*

Algorithms                                                       |      Cost
==========================================================================================
Field arithmetic
------------------------------------------------------------------------------------------
function mulconst (a, c)                                         |   for free
function divconst (a, c)                                         |   for free
                                                                 |
function invert (a)                                              |
------------------------------------------------------------------------------------------
Polynomial arithmetic
------------------------------------------------------------------------------------------                                                                 |
function toom_cook_1_1 (X0,X1,Y0,Y1)                             |   3M
function interpolate(X0, X1, Xm1, Xinf)                          |   for free
function toom_cook_1_2 (X0,X1,Y0,Y1,Y2)                          |   4M
function toom_cook_1_3 (X0,X1,Y0,Y1,Y2,Y3)                       |   5M
function toom_cook_2_2 (X0,X1,X2,Y0,Y1,Y2)                       |   5M
function toom_cook_square_2 (X0,X1,X2)                           |   5SQ
function toom_cook_2_3 (X0,X1,X2,Y0,Y1,Y2,Y3)                    |   6M
function toom_cook_3_3 (X0,X1,X2,X3,Y0,Y1,Y2,Y3)                 |   7M
                                                                 |
function modular_inverse_3n_2 (u0, u1, u2, v0, v1, v2)           |   13M + 2SQ
function modular_inverse_3n_4 (u0, u1, u2, c0, c1, c2, c3, c4)   |   17M + 2SQ
function modular_inverse_3n_3 (u0, u1, u2, c0, c1, c2, c3)       |   16M + 2SQ
                                                                 |
function remainder_4_3n (t0, t1, t2, t3, t4, u0, u1, u2)         |   4M
function quotient_6n_3n (u3, u4, u5, v0, v1, v2)                 |   3M

*/


// ***************************************************************************
// ***************************************************************************
// ***************************************************************************


function mulconst (a, c)
   // returns c*a, where a is supposed to be a field element and c a small
   // constant. Put into a separate function so that each occurrence of
   // "*" in the formulae corresponds to a multiplication of two field
   // elements. It should normally be computed by repeated additions; to
   // simplify, we use a multiplication here.
   return c*a;
end function;


function divconst (a, c)
   // returns a/c, where a is supposed to be a field element and c a small
   // constant. It should normally be computed in a special way, see our
   // article; to simplify, we use a normal division here.
   return a/c;
end function;

function invert (a)
   return 1/a;
end function;

// ***************************************************************************
// ***************************************************************************
// ***************************************************************************

function toom_cook_1_1 (X0,X1,Y0,Y1)
// Let W = X * Y; first multiply without the leading coefficient by
// Cost: 3M
// interpolation on 0, 1 and infinity

Xval1  := X1 + X0;
Yval1  := Y1 + Y0;

// Evaluate

Wval0   := X0 * Y0;
Wval1   := Xval1 * Yval1;
Wvalinf := X1*Y1;

// Interpolate

W2 := Wvalinf;
W0 := Wval0;
W1 := Wval1 - (W0+W2);

return W0,W1,W2;

end function;

// ***************************************************************************
function interpolate(X0, X1, Xm1, Xinf)

// Cost:    for free
// interpolation on 0, 1, -1  and infinity

// Interpolate

W3 := Xinf;
W0 := X0;
W2 := divconst(X1 + Xm1, 2) - W0;
W1 := X1 - ( W0 + W2 + W3 );

return W0,W1,W2,W3;

end function;

function toom_cook_1_1 (X0,X1,Y0,Y1)
// Let W = X * Y; first multiply without the leading coefficient by
// interpolation on 0, 1 and infinity

Xval1  := X1 + X0;
Yval1  := Y1 + Y0;

// Evaluate

Wval0   := X0 * Y0;
Wval1   := Xval1 * Yval1;
Wvalinf := X1*Y1;

// Interpolate

W2 := Wvalinf;
W0 := Wval0;
W1 := Wval1 - ( W0 + W2);

return W0,W1,W2;

end function;

// ***************************************************************************


function toom_cook_1_2 (X0,X1,Y0,Y1,Y2)
// Let W = X * Y; first multiply without the leading coefficient by
// Cost: 4M
// interpolation on 0, 1, -1  and infinity

Xval1  := X1 + X0;
Yval1  := Y2 + Y1 + Y0;
Xvalm1 := - X1 + X0;
Yvalm1 := Y2 - Y1 + Y0;

// Evaluate

Wval0   := X0 * Y0;
Wval1   := Xval1 * Yval1;
Wvalm1  := Xvalm1 * Yvalm1;
Wvalinf := X1*Y2;

// Interpolate

W3 := Wvalinf;
W0 := Wval0;
W2 := divconst(Wval1+Wvalm1,2) - W0;
W1 := Wval1 - ( W0 + W2 + W3 );

return W0,W1,W2,W3;

end function;

// ***************************************************************************

function toom_cook_1_3 (X0,X1,Y0,Y1,Y2,Y3)
// Let W = X * Y; first multiply without the leading coefficient by
// Cost: 5M
// interpolation on 0, 1, -1, 2  and infinity

Xval1  := X1 + X0;
Yval1  := Y3 + Y2 + Y1 + Y0;
Xvalm1 := - X1 + X0;
Yvalm1 := - Y3 + Y2 - Y1 + Y0;
Xval2  := mulconst(X1,2) + X0;
Yval2  := mulconst (Y3, 8) + mulconst (Y2, 4) + mulconst (Y1, 2) + Y0;
//Yval2  := mulconst ( mulconst ( mulconst (Y3, 2) + Y2, 2) + Y1,2) + Y0;

// Evaluate

Wval0   := X0 * Y0;
Wval1   := Xval1 * Yval1;
Wvalm1  := Xvalm1 * Yvalm1;
Wval2   := Xval2 * Yval2;
Wvalinf := X1*Y3;

// Interpolate

W4 := Wvalinf;
W0 := Wval0;
W2 := -(Wval0 + Wvalinf) + divconst(Wval1 + Wvalm1,2);
W3 := - mulconst(Wvalinf,2) + divconst(Wval0 - Wval1 + divconst(Wval2 - Wvalm1,3),2);
W1 := Wval1 - ( W0 + W2 + W3 + W4);

return W0,W1,W2,W3,W4;

end function;

// ***************************************************************************

function toom_cook_2_2 (X0,X1,X2,Y0,Y1,Y2)
// Let W = X * Y; first multiply without the leading coefficient by
// Cost: 5M
// interpolation on 0, 1, -1, 2 and infinity

Xval1  := X2 + X1 + X0;
Yval1  := Y2 + Y1 + Y0;
Xvalm1 := X2 - X1 + X0;
Yvalm1 := Y2 - Y1 + Y0;
Xval2  := mulconst (X2, 4) + mulconst (X1, 2) + X0;
Yval2 :=  mulconst (Y2, 4) + mulconst (Y1, 2) + Y0;
//Xval2  := mulconst (mulconst (X2, 2) + X1, 2) + X0;
//Yval2  := mulconst (mulconst (Y2, 2) + Y1, 2) + Y0;

// Evaluate

Wval0   := X0 * Y0;
Wval1   := Xval1 * Yval1;
Wvalm1  := Xvalm1 * Yvalm1;
Wval2   := Xval2 * Yval2;
Wvalinf := X2*Y2;

// Interpolate

W4 := Wvalinf;
W0 := Wval0;
W2 := divconst (Wval1 + Wvalm1, 2) - (W0 + W4);
W3 := divconst (divconst (Wval2 - Wval1 + Wvalm1 - W0, 2) - mulconst (mulconst (W4, 4) + W2, 2), 3);
W1 := Wval1 - ( W0 + W2 + W3 + W4 );

return W0,W1,W2,W3,W4;

end function;

// ***************************************************************************

function toom_cook_square_2 (X0,X1,X2)
// Let W = X^2 ; first multiply without the leading coefficient by
//   5SQ

// interpolation on 0, 1, -1, 2 and infinity

Xval1  := X2 + X1 + X0;
Xvalm1 := X2 - X1 + X0;
Xval2  := mulconst (X2, 4) + mulconst (X1, 2) + X0;
//Xval2  := mulconst (mulconst (X2, 2) + X1, 2) + X0;

// Evaluate

Wval0   := X0^2;
Wval1   := Xval1^2;
Wvalm1  := Xvalm1^2;
Wval2   := Xval2^2;
Wvalinf := X2^2;

// Interpolate

W4 := Wvalinf;
W0 := Wval0;
W2 := divconst (Wval1 + Wvalm1, 2) - (W0 + W4);
W3 := divconst (divconst (Wval2 - Wval1 + Wvalm1 - W0, 2) - mulconst (mulconst (W4, 4) + W2, 2), 3);
W1 := Wval1 - ( W0 + W2 + W3 + W4 );

return W0,W1,W2,W3,W4;

end function;


function toom_cook_2_3 (X0,X1,X2,Y0,Y1,Y2,Y3)
// Let W = X * Y; first multiply without the leading coefficient by
// interpolation on 0, 1, -1, 2 , -2 and infinity

Xval1  :=  X2 + X1 + X0;
Yval1  :=  Y3 + Y2 + Y1 + Y0;
Xvalm1 :=  X2 - X1 + X0;
Yvalm1 := -Y3 + Y2 - Y1 + Y0;
Xval2  :=  mulconst (X2, 4) + mulconst (X1, 2) + X0;
Yval2  :=  mulconst (Y3, 8) + mulconst (Y2, 4) + mulconst (Y1, 2) + Y0;
Xvalm2 :=  mulconst (X2, 4) - mulconst (X1, 2) + X0;
Yvalm2 := -mulconst (Y3, 8) + mulconst (Y2, 4) - mulconst (Y1, 2) + Y0;

//Evaluate

Wval0   := X0*Y0;
Wval1   := Xval1*Yval1;
Wvalm1  := Xvalm1*Yvalm1;
Wval2   := Xval2*Yval2;
Wvalm2  := Xvalm2*Yvalm2;
Wvalinf := X2*Y3;

// interpolate

W0 := Wval0;
W5 := Wvalinf;
W3 := -mulconst(Wvalinf,5) + divconst(divconst(Wvalm1 - Wval1 + divconst(Wval2 - Wvalm2,2),2),3);
W4 := divconst(divconst(-(Wval1 + Wvalm1)+ divconst( mulconst(Wval0, 3) + divconst(Wval2 + Wvalm2,2) ,2) ,2),3);
W2 := divconst( Wval1 + Wvalm1, 2) -( W0 + W4 );
W1 := Wval1 - ( W0 + W3 + W2 + W4 + W5 );

return W0,W1,W2,W3,W4,W5;

end function;


// ***************************************************************************

function toom_cook_3_3 (X0,X1,X2,X3,Y0,Y1,Y2,Y3)
// Let W = X * Y; first multiply without the leading coefficient by
// interpolation on 0, 1, -1, 2 , -2, 3 and infinity
// 7M

Xval1  :=  X3 + X2 + X1 + X0;
Yval1  :=  Y3 + Y2 + Y1 + Y0;
Xvalm1 := -X3 + X2 - X1 + X0;
Yvalm1 := -Y3 + Y2 - Y1 + Y0;
Xval2  :=  mulconst (X3, 8) + mulconst (X2, 4) + mulconst (X1, 2) + X0;
Yval2  :=  mulconst (Y3, 8) + mulconst (Y2, 4) + mulconst (Y1, 2) + Y0;
Xvalm2 := -mulconst (X3, 8) + mulconst (X2, 4) - mulconst (X1, 2) + X0;
Yvalm2 := -mulconst (Y3, 8) + mulconst (Y2, 4) - mulconst (Y1, 2) + Y0;
Xval3  :=  mulconst (X3, 27)+ mulconst (X2, 9) + mulconst (X1, 3) + X0;
Yval3  :=  mulconst (Y3, 27)+ mulconst (Y2, 9) + mulconst (Y1, 3) + Y0;

//Evaluate

Wval0   := X0*Y0;
Wval1   := Xval1*Yval1;
Wvalm1  := Xvalm1*Yvalm1;
Wval2   := Xval2*Yval2;
Wvalm2  := Xvalm2*Yvalm2;
Wval3   := Xval3*Yval3;
Wvalinf := X3*Y3;

// interpolate

W0 := Wval0;
W6 := Wvalinf;
W4 := -mulconst(Wvalinf,5) + divconst(divconst(-(Wval1+Wvalm1) + divconst(mulconst(Wval0,3) + divconst(Wvalm2+Wval2,2),2),2),3);
W3 := mulconst(mulconst(Wvalinf,3),5) + divconst(divconst(divconst( mulconst(Wval0,5)  - mulconst(Wval1,7) +divconst(- Wval3 + mulconst(Wval2,7) - Wvalm2 - Wvalm1,2),2),2),3);//3
W5 := -mulconst(Wvalinf,3) + divconst(divconst(divconst(Wval1-Wval0 + divconst(Wvalm1-Wval2+ divconst(Wval3-Wvalm2,5),2),2),2),3);
W2 := divconst( Wval1 + Wvalm1, 2) -( W0 + W4 + W6);
W1 := Wval1 - ( W0 + W2 + W3 + W4 + W5 + W6 );

return W0,W1,W2,W3,W4,W5,W6;

end function;

// ***************************************************************************


// ***************************************************************************
// ***************************************************************************
// ***************************************************************************

function modular_inverse_3n_2 (u0, u1, u2, v0, v1, v2)
// For u:= x^3 + u2*x^2 + u1*x + u0 and v:= v2*x^2 + v1*x + v0
// Compute d = gcd (u, v) and s
// such that d = (something)*u + s*v
// note that d is not i.g. the resultant(u,v).

// Cost  13M + 2SQ

// First pseudodivision; quotient into q; interpolation on
// 0, 1 for remainder r

uval1 := u2 + u1 + u0;
vval1 := v2 + v1 + v0;

q1 := v2;
q0 := v2 * u2 - v1;
lc2 := v2^2;
r0 := lc2 * u0 - q0 * v0;
r1 := lc2 * (uval1 + 1) - (q1 + q0) * (vval1) - r0;
// Second pseudodivision; quotient into Q, remainder into d
Q1 := r1 * v2;
Q0 := r1 * v1 - r0 * v2;
lc2 := r1^2;
d := lc2 * v0 - Q0 * r0;
// s = lc2 + Q q
s0 := q0 * Q0;
s2 := q1 * Q1;
s1 := (q0 + q1) * (Q0 + Q1) - s0 - s2;
s0 := s0 + lc2;

return  s0,s1,s2,d;

end function;

function modular_inverse_3n_4 (u0, u1, u2, c0, c1, c2, c3, c4)
// For u:= x^3 + u2*x^2 + u1*x + u0 and c:= c4*x^4 + c3*x^3 + c2*x^2 + c1*x + c0
// Compute d = gcd (u, v) and s
// such that d = (something)*u + s*v
// note that d is not i.g. the resultant(u,v).
// 17M +2SQ

// Euclidian algorithm between c and u

// q1 = quotient of c by u
q11 := c4;
q10 := c3 - c4 * u2;
// r1 = c - q1 u by interpolation on 0, 1, -1
r10 := c0 - q10 * u0;
uval1 := 1 + u2 + u1 + u0;
uvalm1 := -1 + u2 - u1 + u0;
val1 := c4 + c3 + c2 + c1 + c0 - (q11 + q10) * uval1;
valm1 := c4 - c3 + c2 - c1 + c0 - (q10 - q11) * uvalm1;
r11 := divconst (val1 - valm1, 2);
r12 := val1 - r11 - r10;
// q2 = quotient of r12^2 u by r1
q21 := r12;
q20 := r12 * u2 - r11;
// r2 = r12^2 u - q2 r1 by interpolation on 0 and 1
lc2 := r12^2;
r20 := lc2 * u0 - q20 * r10;
r21 := lc2 * uval1 - (q21 + q20) * (r12 + r11 + r10) - r20;
// q3 := quotient of r21^2 r1 by r2
q31 := r21 * r12;
q30 := r21 * r11 - r20 * r12;
lc2 := r21^2;
d := lc2 * r10 - q30 * r20;
// s = r21^2 + q2 q3
s0 := q20 * q30;
s2 := q21 * q31;
s1 := (q21 + q20) * (q31 + q30) - s0 - s2;
s0 := s0 + lc2;

return s0,s1,s2,d;

end function;

function modular_inverse_3n_3 (u0, u1, u2, c0, c1, c2, c3)
// For u:= x^3 + u2*x^2 + u1*x + u0 and c:=  c3*x^3 + c2*x^2 + c1*x + c0
// Compute d = gcd (u, v) and s
// such that d = (something)*u + s*v
// note that d is not i.g. the resultant(u,v).

// 16M + 2SQ

// Euclidian algorithm between c and u

// q1 = quotient of c by u

q10 := c3;
// r1 = c - q1 u by interpolation on 0, 1, -1
r10 := c0 - q10 * u0;
uval1 := 1 + u2 + u1 + u0;
uvalm1 := -1 + u2 - u1 + u0;
val1 := c3 + c2 + c1 + c0 - q10 * uval1;
valm1 := - c3 + c2 - c1 + c0 - q10 * uvalm1;
r11 := divconst (val1 - valm1, 2);
r12 := val1 - r11 - r10;
// q2 = quotient of r12^2 u by r1
q21 := r12;
q20 := r12 * u2 - r11;
// r2 = r12^2 u - q2 r1 by interpolation on 0 and 1
lc2 := r12^2;
r20 := lc2 * u0 - q20 * r10;
r21 := lc2 * uval1 - (q21 + q20) * (r12 + r11 + r10) - r20;
// q3 := quotient of r21^2 r1 by r2
q31 := r21 * r12;
q30 := r21 * r11 - r20 * r12;
lc2 := r21^2;
d := lc2 * r10 - q30 * r20;
// s = r21^2 + q2 q3
s0 := q20 * q30;
s2 := q21 * q31;
s1 := (q21 + q20) * (q31 + q30) - s0 - s2;
s0 := s0 + lc2;

return s0,s1,s2,d;
end function;

// ***************************************************************************
// ***************************************************************************
// ***************************************************************************

function remainder_4_3n (t0, t1, t2, t3, t4, u0, u1, u2)
// For u:= x^3 + u2*x^2 + u1*x + u0 and t:= t4*x^4 + t3*x^3 + t2*x^2 + t1*x + t0
// Compute Remainder(t,u)
//Cost 4M

uval1  := u2 + u1 + u0;
uvalm1 := u2 - u1 + u0;

// q = quotient of t by u
q1 := t4;
q0 := t3 - t4 * u2;
// t = t - q u
T0 := t0 - q0 * u0;
tval1  := (t4 + t3 + t2 + t1 + t0) - (q0 + q1) * (uval1 + 1);
tvalm1 := (t4 - t3 + t2 - t1 + t0) - (q0 - q1) * (uvalm1 - 1);
T1 := divconst (tval1 - tvalm1, 2);
T2 := tval1 - T0 - T1;

return  T0,T1,T2;

end function;

// ***************************************************************************
// ***************************************************************************

function quotient_6n_3n (u3, u4, u5, v0, v1, v2)
// For u:= x^6 + u5*x^5 + u4*x^4 + u3 + ... and v:= x^3 + v2*x^2 + v1*x + v0
// or for u:= x^9 + u5*x^8 + u4*x^7 + u3 * x^6 + ... and v:= x^6 + v2*x^5 + v1*x^4 + v0*x^3
// Compute Quotient(u,v)
//Cost 3M

q2 := u5 - v2;
q1 := u4 - v1 - v2 * q2;
r1 := u3 - v0 - v1 * (u5 - v2);
q0 := - v2 * q1 + r1;

return  q0,q1,q2;

end function;

