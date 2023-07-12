
## Description

Implementation of the algorithm described in our paper [1]:


## Install and Run 

1) Run MAGMA

2) Execute the command AttachSpec("package_spec");

3) To run the main example of our paper, type main(2,0);


## Warnings


This code has only been checked on a limited number of examples as each example
is time consuming to compute. Furthermore, in arithmetic.m, a Weil pairing is used
to speed up the endomorphism ring computation. The fact that the divisors for the
Weil pairing could share a common zero is not accounted for in the current version.

## Code used from other authors

The files addition.m, fieldarithmetic.m, mod_addition.m, mod_fieldarithmetic.m, scalarproduct.m
were written by Stephane Flon, Roger Oyono, and Christophe Ritzenthaler with minor modifications.
This code is based on the paper [2].

The file arita_addition.m contains code from the paper [3].

Some functions from the avisogenies package [4] were used and are marked in the code.

[1] Arora, Sonny, and Kirsten Eisenträger. "Constructing Picard curves with complex multiplication using the Chinese remainder theorem." The Open Book Series 2.1 (2019): 21-36

[2] Flon, Stéphane, Roger Oyono, and Christophe Ritzenthaler. "Fast addition on non-hyperelliptic genus 3 curves." Algebraic Geometry And Its Applications: Dedicated to Gilles Lachaud on His 60th Birthday. 2008. 1-28.

[3] Arita, Seigo, Shinji Miura, and Tsutomu Sekiguchi. "An addition algorithm on the Jacobian varieties of curves." J. Ramanujan Math. Soc 19.4 (2004): 1-17.

[4] Bisson, G., R. Cosset, and D. Robert. "AVIsogenies (abelian varieties and isogenies)." Magma package for explicit isogenies between abelian varieties, http://avisogenies. gforge. inria. fr (2010).
