# L6-representability probe: is M = 15I + J - D16 integrally represented by I_256?

Bounded probe, owner Fable/claude, 2026-09-08.  Local (2-adic + odd-p) representability test of
ONE candidate defect graph at q = 16.  It does not touch the status of A-REG.

## Definitions

* q = 16, n = q^2 = 256.  D16 = circulant graph on Z/256 with connection set
  S = {128, +-1, +-2, +-4, +-6, +-8, +-10, +-12} (15-regular), exactly `circulant_defect(16)` of
  `q_generic_connected_defect_spectral_countermodel.py` (rebuilt independently as a 256x256 integer array;
  checked: diagonal 16, zero exactly on the 15 D-edges of every row, row sum 256).
* M = (q-1) I + J - D16 = 15 I + J - D16 = L_D + J.
* Necessary condition under test.  If A is a symmetric 0/1 matrix with A^2 = M then A^T A = M, so M is
  integrally represented by the standard lattice I_256 (X = A), hence represented over Z_p for every p and
  over Q.  Over Z_2 this says: the lattice L_M = (Z_2^256, M) has an overlattice isometric to I_256, i.e. an
  ODD unimodular overlattice with the Conway-Sloane 2-adic symbol of I_256, namely 1^{+256}_0.

## Step 1: determinant

* det M = 117996544072593761421638769463575875768492182917480033292914820637912365808779360874269150767532122060823145698724112511154298143721857795213580379399508812384107640724769418175455018635408447436430493018864585801442182646678031718833672401773716879446907427636305520177339634909657258060932972544
  (297 digits; fraction-free Bareiss with Python big ints; independently confirmed as the product of the
  cyclotomic resultants Res(Phi_d, f), d | 256, of the circulant generating polynomial f).
* v_2(det M) = 24.  det M / 1024 = s^2 with
  s = 339456919315091211970607438028339390145374422467729873606251561512864915025951141643271973889924583032275034770193582858448956075643263020240397184,
  so det M = 2^10 * s^2 as the campaign's spectral factorisation (x-256)(x-4)P(x)^2 requires.
* Odd part of det M is 1 mod 8 and equals
  7^2 * 17^2 * 127^2 * 1871^2 * 36353^2 * 674565247^2 * C127^2, where C127 is a 127-digit cofactor left by
  trial division to 1e6; a bounded ECM run (`ecm_cofactor.py`, 36 s) split it completely:
  C127 = 10917093409919 * 1134649554167807 * 127870103902581011201 (probable prime; conditional) * P76 with
  P76 = 2414616786049174212391303257912964622140651504647957347911167950708516357887.
  Eight of the ten odd prime factors (7, 17, 127, 1871, 36353, 674565247, 10917093409919, 1134649554167807; all below 2^64, deterministic sympy.isprime) are proven primes; the two large factors 127870103902581011201 and the 76-digit cofactor are BPSW probable primes without certificates (their rows in the Hasse table are CONDITIONAL on primality). Each factor has exponent 2, consistent with det M/1024
  being a square.  M is positive definite (all 256 leading principal minors positive).

## Step 2: 2-adic Jordan decomposition of M

Symmetric congruence reduction over Z_2 modulo 2^112 with explicit precision bookkeeping
(P^T M P = J verified modulo 2^precP), then invariants per constituent.

    2-adic symbol of M :   1^{-254}_{II}  256^{-1}_{3}  65536^{+1}_{1}

i.e. M ~ (even unimodular of rank 254 with det = 3 mod 8, i.e. H^126 + A_2)  +  <2^8 * u>  +  <2^16 * u'>
with u = 3 mod 8, u' = 1 mod 8.  Consistency: 8 + 16 = 24 = v_2(det M).  The scale-0 constituent is of
type II because M has even diagonal (16) — M mod 2 is alternating of rank 254.  So the 2-part of the
discriminant group is Z/2^8 x Z/2^16 (compare q = 4 in the campaign's discriminant-form audit: Z/2^4 x Z/2^8).

## Step 3: overlattice chain (metabolicity at 2)

Greedy enlargement in Jordan coordinates (recompute the Jordan form after each step):

    steps 1..12: adjoin e/2 on the rank-1 block of scale 2^16, 2^14, 2^12, 2^10, 2^8, 2^8, 2^6, 2^6, 2^4, 2^4, 2^2, 2^2

(integrality of every new Gram verified).  After 12 steps the lattice is UNIMODULAR:
index [U : L_M] = 2^12 = 2^{v_2(det M)/2}, as required.  Hence the 2-primary discriminant form of M is
METABOLIC (an explicit Lagrangian of order 2^12 is the chain above); no stall, no anisotropic core.
The final U is ODD (type I).

## Step 4: invariants of the unimodular overlattice U

Explicit diagonalisation of U over Z_2 (R^T U R = diag verified modulo 2^88):

    diagonal units mod 8 : {1: 52, 3: 82, 5: 58, 7: 64}
    det U = 1 mod 8  (sign +; forced: det U = det M / 2^24 up to unit squares, and the odd part of det M is 1 mod 8)
    oddity(U) = 52*1 + 82*3 + 58*5 + 64*7 = 1032 = 4 mod 8

    2-adic symbol of U :   1^{+256}_{4}          (I_256 has symbol 1^{+256}_{0})

Odd unimodular Z_2-lattices of equal rank are isometric iff their symbols (rank, sign, oddity) agree
(Conway-Sloane, Sphere Packings, Lattices and Groups, ch. 15 sec. 7, Theorem 10; a single constituent admits no
sign walking / oddity fusion, so the symbol is already canonical; equivalently O'Meara 93:16).  Therefore
U ~ I_254 + <3,3>, and U is NOT isometric to I_256.

This does not depend on the Lagrangian chosen: every odd unimodular overlattice U' of L_M satisfies
U' (x) Q_2 ~ M (x) Q_2, and for odd unimodular Z_2-lattices the pair (det class, oddity) is equivalent to the
pair (det class, Hasse-Witt invariant) (for a diagonalisation <e_1..e_n>: c_2 = (-1)^{C(k,2)} with
k = #{e_i = 3 mod 4}, oddity = sum e_i mod 8; replacing <1,1> by <3,3> flips both).  Here k = 82 + 64 = 146,
C(146,2) = 10585 is odd, so c_2(U) = -1, in agreement with the direct computation c_2(M) = -1 below, while
c_2(I_256) = +1.  So NO overlattice of L_M is isometric to I_256: M is not Z_2-represented by I_256.

## Step 5: rational Hasse-Witt invariants (all places)

Diagonalise M over Q: d_k = Delta_k / Delta_{k-1} (leading principal minors from Bareiss), square class
d_k ~ Delta_k Delta_{k-1}; c_p(M) = prod_{i<j} (d_i, d_j)_p.  I_256: c_p = +1 at every place, det = 1.

    place      c_p(M)    c_p(I_256)
    infinity   +1        +1     (M positive definite)
    2          -1        +1
    7          -1        +1
    17         +1        +1
    127        -1        +1
    1871       -1        +1
    36353      +1        +1
    674565247  -1        +1
    10917093409919          -1   +1
    1134649554167807        -1   +1
    127870103902581011201   +1   +1
    P76 (76 digits, above)  -1   +1
    p not dividing 2 det M: +1 (p-unimodular); spot-checked at 3,5,11,13,19,23.

Cross-checks: (i) c_2 recomputed from the 2-adic Jordan symbol of M (H^126 + A_2 + <3> + <1> rationally)
gives -1; (ii) every odd c_p recomputed from an independent p-adic Jordan diagonalisation (each listed p has
p-part of rank 2, valuation 1) agrees; (iii) all values are invariant under a random integral unimodular
congruence R^T M R; (iv) the product over ALL places (infinity, 2, and the ten odd primes) is +1, as Hilbert
reciprocity demands (c_2 = -1 and exactly seven odd primes with c_p = -1). det M = 2^10 s^2 is a rational square, so det classes agree at every place, and the
only obstruction is the Hasse invariant.

Since two nondegenerate quadratic forms over Q_p of the same rank are equivalent iff they have the same
determinant class and Hasse invariant (Serre, A Course in Arithmetic, ch. IV, Thm. 7), M (x) Q_p is NOT
equivalent to I_256 (x) Q_p for p = 2, 7, 127, 1871, 674565247, 10917093409919, 1134649554167807, P76; by Hasse-Minkowski (ibid. Thm. 9) M is not
rationally equivalent to I_256 either.  The campaign's 2ADIC_TERMINAL audit computed the rational congruence
only for its q = 8 looped control (where it holds); for D16 at q = 16 it fails.

## Verdict

**NOT REPRESENTED.**  There is no matrix X over Z_2 with X^T X = M, because c_2(M) = -1 ≠ c_2(I_256) makes M and I_256 non-isometric over Q_2 (a local statement); and there is no matrix X over Q with X^T X = M by Hasse–Minkowski (the same local invariant, together with the odd-prime ones, decides the global class), so a fortiori none over Z. Hence D16 is
excluded as the defect graph of any symmetric integral square root A with A^2 = 15I + J - D16, in particular
of any A-REG adjacency matrix.  The obstructing invariant is the Hasse-Witt invariant: c_p(M) = -1 at
p = 2, 7, 127, 1871, 674565247, 10917093409919, 1134649554167807 and P76 (any single one suffices).  At the 2-adic lattice level the picture is:
the discriminant form IS metabolic (unimodular odd overlattice of index 2^12 exists), but its odd unimodular
overlattices all have symbol 1^{+256}_4 (oddity 4, not 0) — the integral 2-adic refinement adds nothing
beyond the rational condition at 2, and the odd primes obstruct just as well.

Calibration / scope.  D16 has R = {1,2,4,6,8,10,12} with exactly one odd representative, so it was already
excluded by the mod-2 alternating-square-root proposition of NONBIP_CONNECTED_2ADIC_TERMINAL_AUDIT.md
(re-verified here: M mod 2 is nilpotent of index 128 with nullity 2, `mod2_check.py`).  The present
obstruction is independent of that one (it ignores the zero-diagonal requirement entirely) and is stronger
in one respect (rules out every symmetric integral square root, looped or not) but it is a statement about
ONE circulant candidate at q = 16.  It says nothing about A-REG, about non-circulant defects, about other
q, or about whether every relevant D fails the Hasse test (the q = 8 looped control shows some circulant
defects pass it).

## Theorems relied on

* Conway-Sloane, SPLAG ch. 15 sec. 7 (2-adic symbols; Theorem 10: equivalence of 2-adic forms iff equivalent
  symbols); O'Meara, Introduction to Quadratic Forms, 93:16 / 93:28 (classification of unimodular Z_2-lattices).
* Serre, A Course in Arithmetic, ch. IV: Thm. 7 (rank, det, Hasse invariant classify forms over Q_p),
  Thm. 9 (Hasse-Minkowski), Hilbert symbol formulas (ch. III, Thm. 1).
* Overlattice / Lagrangian correspondence: unimodular overlattices of L correspond to subgroups H of L^#/L
  with H = H^perp for the discriminant bilinear form (Nikulin, Izv. 1979, sec. 1).

## Files

* `l6probe.py` — the probe (steps 1-5; `--crosscheck` appends the independent cross-checks and the script hash).
* `results.json` — all numerical results (contains `script_sha256`).
* `unit_tests.py` — machinery tests on small lattices with known symbols/invariants, including the
  end-to-end control: a random B^T B (12x12) yields an odd unimodular overlattice with symbol 1^{+12}_4 = symbol of I_12.
* `mod2_check.py` — independent verification of the mod-2 obstruction on D16.
* `ecm_cofactor.py` / `ecm_cofactor.json` — bounded ECM factorisation of the cofactor C127 (complete).
* `extra_primes.py` — Hasse invariants at the four ECM primes (two routes), merged into `results.json`.
* `run.log`, `crosscheck.log`, `unit_tests` output.

## SHA-256

    9df982da2536a32148b7b6ec6f8d54f4c9555a4736d3c05c9d8b62b59fee0a4a  l6probe.py
    98175679c8ffa5dd0a4f9f876d1ae6a35a2645e9ba6007a8359392583f1ec365  extra_primes.py
    91c1e7b12dd6111536877976feccc6283949c3098c928d96ef9b8afb66535709  unit_tests.py
    cbb4abdfca5f71a69f6094899956466b63c8c1fdcee9bb3309cc35514a812435  mod2_check.py
    a156e2cfa55c5d176b8051f160f6aee89d4026065230ac64b0785beee320cf5d  ecm_cofactor.py
    b43e73da2b56465ed0ee1af1b55e37923696f79857a23d31e78c6118d4086826  results.json
    9a361181dc63610590cf38a36b43900fb422ee8b24b67e6f332837d165ece1a6  ecm_cofactor.json

**Primality caveat (review #1536, sol-1):** SymPy `isprime` is deterministic only below 2^64; the eight factors below 2^64 (7, 17, 127, 1871, 36353, 674565247, 10917093409919, 1134649554167807) are proven primes, while the two large factors 127870103902581011201 and the 76-digit cofactor are BPSW *probable* primes without a certificate. The obstruction does not depend on them: c_2(M) = −1 ≠ c_2(I_256) already decides non-congruence, and the Hasse invariants at the six small proven primes are computed independently of the large factors.

**Editorial conditions (review #1536, sol-1):** (1) "metabolic" refers throughout to the discriminant BILINEAR form (L^#/L, b) with b(x,y) = xᵀMy mod Z₂, not to a quadratic refinement. (2) The non-existence of a Z₂-representation XᵀX = M is asserted on the LOCAL ground c₂(M) = −1 ≠ c₂(I₂₅₆) (M and I₂₅₆ are not isometric over Q₂, so no X ∈ M₂₅₆(Z₂) ⊂ M₂₅₆(Q₂) can exist); the global statement "no rational X" is the Hasse–Minkowski consequence of the same local data and is not itself the source of the Z₂ claim. (3) Sol-1 independently reproduced every tabulated Hasse invariant (cumulative Hilbert symbols on an exact Bareiss diagonalisation) and the index-2¹² odd unimodular overlattice of determinant 1 and oddity 4 by a 64-bit 2-adic Schur reduction (127 even unimodular blocks of aggregate determinant 3 mod 8, tail scales 8 and 16 with units 3 and 1), with the classification reference Allcock–Gal–Mark Thm 3.1; the large-factor places remain conditional on BPSW probable-primality.
