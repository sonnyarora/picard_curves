AUTHOR: Sonny Arora

======================================
Run instructions
======================================

1) Run MAGMA

2) Execute the command AttachSpec("package_spec");

3) To run the main example of our paper, type main(2,0);

======================================
Warnings
======================================

This code has only been checked on a limited number of examples as each example
is time consuming to compute. Furthermore, in arithmetic.m, a Weil pairing is used
to speed up the endomorphism ring computation. The fact that the divisors for the
Weil pairing could share a common zero is not accounted for in the current version.

======================================
Code used from other authors
======================================

The files addition.m, fieldarithmetic.m, mod_addition.m, mod_fieldarithmetic.m, scalarproduct.m
were written by Stephane Flon, Roger Oyono, and Christophe Ritzenthaler with minor modifications.
This code is based on the paper [1].

The file arita_addition.m contains code from the paper [2].

Some functions from the avisogenies package [3] were used and are marked in the code.

[1] Flon, St�phane, Roger Oyono, and Christophe Ritzenthaler. "Fast addition on non-hyperelliptic genus 3 curves." Algebraic Geometry And Its Applications: Dedicated to Gilles Lachaud on His 60th Birthday. 2008. 1-28.

[2] Arita, Seigo, Shinji Miura, and Tsutomu Sekiguchi. "An addition algorithm on the Jacobian varieties of curves." J. Ramanujan Math. Soc 19.4 (2004): 1-17.

[3] Bisson, G., R. Cosset, and D. Robert. "AVIsogenies (abelian varieties and isogenies)." Magma package for explicit isogenies between abelian varieties, http://avisogenies. gforge. inria. fr (2010).