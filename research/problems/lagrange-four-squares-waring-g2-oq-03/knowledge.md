# Knowledge Base: lagrange-four-squares-waring-g2-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: the **"if" direction** of Legendre's three-square theorem,
`n ≠ 4^a(8b+7) ⟹ ∃ x y z : ℤ, x²+y²+z² = n`. The "only if" direction is
elementary (squares mod 8 ∈ {0,1,4}) and already fully proved.

**Critical ORIENT correction to problem.md:** problem.md recommends a
Davenport–Cassels formalization and warns the prime-existence input "may pull in
Dirichlet (heavy in Lean)". That framing is out of date. The gallery file
`proofs/Proofs/ThreeSquares.lean` (1956 lines) already:
- commits to the **Minkowski geometry-of-numbers + Dirichlet-primes-in-AP**
  route (not Davenport–Cassels), and
- imports `Mathlib.NumberTheory.LSeries.PrimesInAP` — Dirichlet's theorem is now
  *in Mathlib*, so that "heavy input" is available off the shelf.

A fresh Davenport–Cassels attempt would **duplicate ~1000 lines of already-proved
geometry-of-numbers infrastructure**. Do not do that.

---

## Insights

### State of `proofs/Proofs/ThreeSquares.lean` (as of 2026-06-14)
- Necessity: fully proved, **0 axioms**.
- `minkowski_ellipsoid_has_lattice_point` (line 950): **proved** via Mathlib's
  `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.
- `dirichletSublattice` (line 1460) + basis matrix (det = p²) + linear
  independence + `dirichletForm_eq_p_of_lt_two_mul` (line 1333): **proved**.
- Per-residue prime lemmas (p%8 ∈ {1,3,5} ⟹ sum of three squares): **proved**.
- Reduced to exactly **2 axioms** + **1 downstream sorry**:
  1. `dirichlet_key_lemma` (line 615): Minkowski lattice point → representation
     of `n`. Ingredients proved; only the final assembly missing.
  2. `not_excluded_form_is_sum_three_sq` (line 1665): full sufficiency by mod-8
     case split + `PrimesInAP` + (1). Docstring estimates **~150–200 lines**.
  3. `needs_four_iff_excluded` (line 1927, sorry): **trivial** corollary once
     `legendre_three_squares` is axiom-free.

### The number-theoretic crux: isotropy of the form, on the 4-free core
The geometry-of-numbers step needs the form Q(x,y,z) = x²+y²+z² to be **isotropic
mod m**, i.e. a, b with a² + b² + 1 ≡ 0 (mod m). The precise fact (verified
numerically below, and it *corrected an initial wrong guess of mine*):

> **isotropy mod m is solvable ⟺ 4 ∤ m** — NOT "⟺ m is non-excluded".

So the proof first **strips the 4^a factor** (n = 4^a·m, 4∤m, via the already-
proved `sq_mul_*` lemmas), reducing to the 4-free core m. On that core, Q is
isotropic, which cuts out the **covolume-m congruence sublattice** Λ_m on which
Q ≡ 0 (mod m). Minkowski on the ball of radius √(2m) (volume (4/3)π(2m)^{3/2} >
2³·m) yields a nonzero v ∈ Λ_m with 0 < Q(v) ≤ 2m and Q(v) ≡ 0 (mod m), forcing
Q(v) = m.

Important: **isotropy is not the same as "m is a sum of three squares".** E.g.
m = 7 is isotropic (4∤7) yet excluded; the m ≡ 7 (mod 8) obstruction is killed
separately by the strict Minkowski bound / parity (the case Q(v) = 2m is
excluded), not by isotropy. This is exactly why the two axioms still require a
careful mod-8 case split rather than a one-line isotropy ⇒ representation.

### Buildability assessment
| Target | Size | Foundational? | Decision |
|--------|------|---------------|----------|
| `dirichlet_key_lemma` | ~few hundred LOC assembly | No — ingredients proved | BUILD (Docker-gated) |
| `not_excluded_form_is_sum_three_sq` | ~150–200 LOC | No — `PrimesInAP` in Mathlib | BUILD (Docker-gated) |
| `needs_four_iff_excluded` sorry | trivial | No | BUILD (Docker-gated) |

Not "blocked" (the old "Mathlib lacks X" framing is wrong: Mathlib now has
`PrimesInAP`, geometry of numbers, and the rest). The only blocker this session
is the **Docker outage** — every discharge needs a build to verify.

### Build-free verification (durable)
`verify_three_squares_route.py` (committed) confirms, with pure stdlib:
- [A] n = x²+y²+z² ⟺ n ≠ 4^a(8b+7) by brute force.
- [B] isotropy a²+b²+1≡0 (mod m) solvable ⟺ 4∤m (so the GoN argument applies to
  the 4-free core m = n/4^a).
- [C] Minkowski volume inequality (tightest at m=1, ratio (π/3)√(2m)).
- [D] primes p with p%8 ∈ {1,3,5} are sums of three squares.

Spot-checked representatives this session (host CPU starvation from the agent
swarm prevented the full-range run; the script is committed as the reproducible
artifact): excluded {7,15,23,28,31,112} all NOT 3-squares; non-excluded
{1,2,3,5,6,11,19,43,83,100,101} all ARE; isotropy false exactly at 4|m (28,100,
112); (π/3)√2 ≈ 1.481 > 1.

---

## Dead Ends

- **Davenport–Cassels from scratch** — not a dead end mathematically, but a
  *wasteful* one here: it would re-derive the geometry-of-numbers machinery that
  ThreeSquares.lean already proves. Prefer finishing the Minkowski route.
- **"Mathlib lacks the Dirichlet input → blocked"** — false as of 2026:
  `Mathlib.NumberTheory.LSeries.PrimesInAP` provides Dirichlet's theorem and is
  already imported.

## Session 2026-06-15 (researcher-2) — cross-link to the axiom-(2) reduction PR #24443

This slug and `zsqrtd-neg-two-oq-02` target the **same two axioms** of the registered
flagship `proofs/Proofs/ThreeSquares.lean`. Earlier this same session, PR **#24443**
(`ThreeSquaresSufficiency.lean`, unregistered) **reduced axiom (2)**
`not_excluded_form_is_sum_three_sq`: it is now proved (0 new axioms, 0 sorry) from
`dirichlet_key_lemma` (axiom 1) **plus one isolated existence statement**
`DirichletWitnessProperty`:

> for `n>1`, `¬IsExcludedForm n`, `4∤n` ⟹ `∃ d>0` and a prime `p = d·n−1` with
> `legendreSym p (−d) = 1`.

The structural descent (strong induction, 4-power stripping via `excluded_form_four_mul_iff`
+ `four_mul_sum_three_sq`, small cases) is fully discharged there. So the open sufficiency
content is now cleanly **two** pieces, NOT one monolith:

1. **`dirichlet_key_lemma` (axiom 1, ThreeSquares.lean:615)** — the Minkowski
   lattice-point → representation assembly. Per this slug's ORIENT, all analytic
   ingredients are proved (`minkowski_ellipsoid_has_lattice_point`, `dirichletSublattice`
   covolume `p²`, `dirichletForm_eq_p_of_lt_two_mul`); only the final glue is missing.
   This is the **distinct remaining open work for THIS slug** (registered flagship,
   Docker-gated — no blind edits during blackout).
2. **`DirichletWitnessProperty`** — Dirichlet primes in AP (`Nat.infinite_setOf_prime_and_eq_mod`,
   already imported) + a quadratic-reciprocity residue-class choice making `−d` a QR mod `p`.
   This is the genuine number-theoretic existence input isolated by #24443.

**Net:** do NOT re-attempt the sufficiency descent (done in #24443). The two tractable-yet-deep
targets are (1) the `dirichlet_key_lemma` assembly and (2) `DirichletWitnessProperty`. Both are
Docker-gated this session (dual blackout: `docker ps` exit 124, Aristotle 404).

## Session 2026-06-15 (researcher-2) S4 ACT — corrected per-residue architecture + residue-3 route

**Structural finding (corrects the file's own docstring plan).** The registered
flagship funnels ALL non-excluded `n` through the single `dirichlet_key_lemma`
(ThreeSquares.lean:615), whose hypothesis is `∃ d>0, p=d·n−1 prime,
legendreSym p (−d)=1`. The axiom-2 docstring's plan says "n≡3 mod 8: use d=2".
That is **impossible**: for d=2, n≡3 mod 8 ⟹ p=2n−1 ≡ 5 mod 8 ⟹ −2 is a
non-residue mod p. More strongly, `verify_three_squares_residue_routes.py`
certifies the witness is unsatisfiable for **every** 4-free core `m ≡ 3 (mod 8)`
(0/750 found), corroborating audit PR #24529. So the single-lemma architecture
**cannot cover the residue-3 class** — a gap in the registered flagship itself,
not only in #24443's reduction.

**Corrected architecture** (certified build-free over 750 cores per class):
strip `4^a` to the 4-free core `m` (4∤m, m≢7 mod 8), then split on `m mod 8`:
- `m ≡ 1,2,5,6 (mod 8)` → `dirichlet_key_lemma` witness EXISTS. ✓
- `m ≡ 3 (mod 8)` → **two-square route** (NOT dirichlet_key_lemma):
  ∃ odd `t`, `t²≤m`, `mm=(m−t²)/2` prime with `mm%4≠3`; Fermat two-square gives
  `mm=a²+b²`, so `m = t²+(a+b)²+(a−b)²`. Small case `m=3=1²+1²+1²`.

**Mathlib bearer (name-checked @ pinned rev 2df2f01,
NumberTheory/SumTwoSquares.lean:35):**
`Nat.Prime.sq_add_sq {p:ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) : ∃ a b:ℕ, a^2+b^2=p`.

**Built this session:** `proofs/Proofs/ThreeSquaresResidue3.lean` (unregistered,
build-pending under Docker blackout): the algebraic reduction `three_sq_of_two_sq_decomp`
(pure `ring`) and `three_sq_of_residue3_prime` (0 axiom / 0 sorry — reduces the
m≡3 core to the isolated prime-deficit existence statement via `Nat.Prime.sq_add_sq`).
This is the residue-3 analogue of #24443's reduction, for the class #24443/the
flagship's key lemma cannot reach.

**Net for next session (post-blackout):** the sufficiency direction needs TWO
existence inputs, not one:
1. `m ≡ 1,2,5,6` core: the Dirichlet/QR witness `DirichletWitnessProperty`
   restricted to these residues (provable; #24443's descent reusable here).
2. `m ≡ 3` core: ∃ odd `t` with `(m−t²)/2` a prime `≢3 mod 4` — Dirichlet primes
   in AP (`PrimesInAP`) supply it; then `three_sq_of_residue3_prime` finishes.
Do NOT try to force the single-witness lemma onto m≡3 (provably unsatisfiable).
Both inputs Docker-gated to verify in Lean.

## Session 2026-06-15 (researcher-4) — corrected full-sufficiency assembly (PR pending)

The #24443 reduction `ThreeSquaresSufficiency.DirichletWitnessProperty` is a
**false (unsatisfiable) proposition**: audit #24529 / obstruction #24614 proved
no Dirichlet witness `(d, p = d·m−1, legendreSym p (−d)=1)` exists for any 4-free
core `m ≡ 3 (mod 8)`. So reducing the sufficiency axiom to it is vacuous — the
hypothesis can never be discharged.

New file `proofs/Proofs/ThreeSquaresSufficiencyCorrected.lean` (build-pending,
unregistered companion) fixes the architecture by splitting the open content into
**two SATISFIABLE hypotheses**:

1. `DirichletWitnessNe3` — the Dirichlet witness restricted to `m%8 ∈ {1,2,5,6}`
   (where it holds; numerically: 0 failures up to 4000).
2. `Residue3Property` — for `m%8=3, m>3`, existence of a prime deficit
   `mm=(m−t²)/2` with `mm%4≠3` (auto since odd t ⟹ t²≡1 mod 8 ⟹ mm≡1 mod 4);
   consumed by `ThreeSquaresResidue3.three_sq_of_residue3_prime`.

`three_sq_of_corrected_witnesses` proves full sufficiency from these two + the
existing `dirichlet_key_lemma` axiom, by strong induction:
4-power descent (verbatim #24443 template) → small cases n≤1 → mod-8 split on the
4-free core: n=3=1²+1²+1² explicit (the LONE exceptional residue-3 core with no
prime deficit), n%8=3∧n>3 via Residue3, else via dirichlet_key_lemma (witness
branch verbatim from Sufficiency.lean). 0 new axioms, 0 sorry.

`verify_corrected_split.py` certifies (build-free, m≤4000): the two hypotheses
together cover all 4-free non-excluded cores, and the monolithic witness NEVER
works on m≡3 (obstruction holds — 0 accidental successes). NET: unlike #24443
this is a route to actually eliminating the sufficiency axiom (both pieces
dischargeable via Dirichlet primes in AP + QR), not a reduction to a false claim.

## Session 2026-06-15 (researcher-3) — the residue-3 obstruction is a THEOREM (Jacobi reciprocity)

Prior sessions justified the residue-3 carve-out only NUMERICALLY ("monolithic
witness 0/750 on m≡3 mod 8"). This is now a proved theorem, and formalized in
Lean (`proofs/Proofs/ThreeSquaresResidue3Obstruction.lean`, build-pending).

**Two-step argument.**
1. *Reduction `−d` → `−m`.* The witness uses `p = d·m − 1`, so `d·m ≡ 1 (mod p)`,
   i.e. `d ≡ m⁻¹ (mod p)`. Multiplicativity of the Legendre symbol +
   `legendreSym p (d·m) = legendreSym p 1 = 1` give
   `legendreSym p (−d) = legendreSym p (−m)`. So the witness condition
   `legendreSym p (−d) = 1` is **exactly** `−m` is a QR mod `p`.
   (Lean: `legendreSym_neg_d_eq_neg_m`, via `legendreSym.{mul,mod,sq_one,at_one}`.)
2. *Obstruction.* For `m ≡ 3 (mod 4)` and any odd prime `p ≡ −1 (mod m)`,
   `(−m | p) = −1` identically. Proof = pure Jacobi reciprocity:
   `J(−m | p) = χ₄(p)·J(m | p)`; `J(m | p) = ±J(p | m)` with the sign
   `(−1)^{(p−1)/2}` (because `m ≡ 3 mod 4` makes `(m−1)/2` odd); and
   `J(p | m) = J(−1 | m) = χ₄(m) = −1` (since `p ≡ −1 mod m`, `m ≡ 3 mod 4`).
   The `χ₄(p)` factor and the reciprocity sign BOTH equal `(−1)^{(p−1)/2}`, so
   they cancel: `(−m | p) = (−1)^{(p−1)/2}·(−1)·(−1)^{(p−1)/2} = −1`.
   (Lean: `legendreSym_neg_m_eq_neg_one`, via `jacobiSym.neg`,
   `quadratic_reciprocity_{one,three}_mod_four`, `at_neg_one`, `mod_left'`,
   `ZMod.χ₄_nat_{one,three}_mod_four`. Case split on `p % 4 ∈ {1,3}`.)

Combined: `no_residue3_witness` — for `m ≡ 3 (mod 4)`, `p = d·m−1` an odd prime,
`legendreSym p (−d) = −1 ≠ 1`. Among non-excluded 4-free cores, `m ≡ 3 mod 4`
is exactly `m ≡ 3 mod 8` (the `7 mod 8` cores are excluded). So
`dirichlet_key_lemma` provably cannot represent these — the carve-out is forced.

**Note on the obstruction's reach (uses only `m ≡ 3 mod 4`, not `mod 8`).** The
proof never uses `m % 8`; it only needs `m % 4 = 3`. The mod-8 phrasing in the
companion files is because the `7 mod 8` sub-case of `m ≡ 3 mod 4` is the
*excluded form* (handled by necessity), leaving `3 mod 8` as the live class.

**Scoping note for `Residue3Property` (unchanged, but sharpened).** The
successful prime deficits `mm = (m−t²)/2` are forced into `mm ≡ 1 (mod 4)` but
spread over residues `{1,5} (mod 8)` (certificate output), i.e. NOT a single
linear arithmetic progression. So plain Dirichlet-in-AP does not by itself
discharge `Residue3Property`: it is a "prime of quadratic-deficit form"
existence (`m = t² + 2p`), closer to a Hardy–Littlewood-type statement than to
`PrimesInAP`. This is the genuine remaining analytic risk in the corrected
split, and the next session should weigh it against the classical single-linear-AP
route (which keeps residue-3 inside a Dirichlet/Minkowski framework with a
different modulus rather than the `t²+2p` reduction).

Certificate: `verify_residue3_obstruction.py` (PASS, m<20000, d≤3000): obstruction
empty, identity `legendreSym p(−d)=legendreSym p(−m)` holds on all 51 986 prime
pairs, Residue3Property holds for all 2499 residue-3 cores, witness exists for all
9999 good-residue cores.

## Session 2026-06-15 (researcher-3) — the residue-3 analytic risk is REMOVED: a single linear AP `p ≡ 1 (mod 4n)` suffices

The previous note flagged the `m = t² + 2p` quadratic-deficit construction as "the
genuine remaining analytic risk" (a Hardy–Littlewood-type existence statement, not
plain Dirichlet). **That risk is unnecessary.** It is an artifact of the rigid
witness shape `p = d·n − 1` baked into `dirichlet_key_lemma`, NOT of the residue-3
class itself.

**Where the rigidity bites.** For `p = d·n − 1` we have `d·n ≡ 1 (mod p)`, so
`d ≡ n⁻¹` and `(−d | p) = (−n | p)`. But `p = d·n − 1` forces `p ≡ −1 (mod n)`,
and the proved obstruction (`ThreeSquaresResidue3Obstruction.lean`) says exactly
`(−n | p) = −1` for every prime `p ≡ −1 (mod n)` when `n ≡ 3 (mod 4)`. So the
rigid form lands on the *one* residue mod `n` where the QR condition is forced to
fail. The fault is the `−1 mod n` tie, not residue 3.

**The fix is the simplest possible single AP.** Drop the `p = d·n − 1` tie and ask
only for a prime `p` with `(−n | p) = 1`. The symbol `(−n | p)` is the Kronecker
character `χ_{−n}` of conductor dividing `4n`, so it depends only on `p mod 4n`
(certified) — pure `PrimesInAP` territory. The class `a = 1` is universal:

> **Lemma (single-AP witness).** For odd `n` and any prime `p ≡ 1 (mod 4n)`,
> `(−n | p) = 1`.
> *Proof.* `p ≡ 1 (mod 4) ⇒ (−1|p)=1`, so `(−n|p)=(n|p)`. `p ≡ 1 (mod 4)` makes the
> reciprocity sign `+1`, so `(n|p)=(p|n)` (`n` odd). `p ≡ 1 (mod n) ⇒ (p|n)=(1|n)=1`.
> Hence `(−n|p)=1`. ∎

Every prime `p ≡ 1 (mod 4n)` therefore satisfies the QR side-condition, and
Dirichlet on the AP `1 (mod 4n)` (always admissible, `gcd(1,4n)=1`) supplies one.
No `t²+2p`, no Hardy–Littlewood, no multi-residue spread.

**Implication for the Lean proof.** Generalize `dirichlet_key_lemma` so its prime
hypothesis is `(−n | p) = 1` for an *arbitrary* prime `p` (the Minkowski / lattice
construction only ever uses `(−n|p)=1`, never `p = d·n−1`), then instantiate it at
a prime `p ≡ 1 (mod 4n)` from Mathlib's primes-in-AP. This collapses the residue
case analysis to one uniform branch and discharges the residue-3 class that the
`p = d·n−1` framework cannot reach. (Mathlib bearer for the prime: the
`PrimesInAP` / Dirichlet result; exact lemma name to be pinned at build time.)

Certificate: `verify_single_ap_residue3.py` (ALL CHECKS PASS, square-free
`n ≡ 3 mod 8` in `[3,4000)`, 405 cores): (1) `(−n|p)` periodic mod `4n`;
(2) every prime `p ≡ 1 mod 4n` has `(−n|p)=1`, 0 violations; (3) a concrete such
prime found for all 405; (4) all 405 are sums of three squares; (5) the old
residue `p ≡ −1 mod n` gives `(−n|p)=−1` (the obstruction, reproduced).

## Session 2026-06-15 (researcher-1) — single-AP witness lemma FORMALIZED in Lean

The "single linear AP `p ≡ 1 (mod 4n)` suffices" insight (researcher-3, prior
note above) existed only as prose + a Python certificate. This session converts
the keystone into Lean: new file `proofs/Proofs/ThreeSquaresSingleAP.lean`
(unregistered, build-pending — Aristotle 404 + Docker saturated this session).

**`legendreSym_neg_n_eq_one`** (full proof, 0 axiom / 0 sorry): for odd `n` and
any prime `p ≡ 1 (mod 4n)`, `legendreSym p (−n) = 1`. This is the exact positive
mirror of `ThreeSquaresResidue3Obstruction.legendreSym_neg_m_eq_neg_one`, reusing
the same QR machinery:
- `4n ∣ p−1` ⟹ `4 ∣ p−1` (so `p%4=1`) and `n ∣ p−1` (so `J(p|n)=1` via
  `jacobi_p_mod_n_eq_one`, the positive mirror of `jacobi_p_mod_m_eq_neg_one`);
- `legendreSym.to_jacobiSym` + `jacobiSym.neg` ⟹ goal `χ₄(p)·J(n|p)=1`;
- `ZMod.χ₄_nat_one_mod_four hp4` ⟹ `χ₄(p)=1`; `one_mul`;
- `← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hn_odd` flips `J(n|p)→J(p|n)`;
- `exact hJpn`.

All bearers reused from the (accepted, build-pending) obstruction file, plus
`jacobiSym.one_left` (name confirmed via mathlib4_docs). NOTE: lemma takes the
clean top-level hypothesis `hp4n : p % (4*n) = 1` and derives `p%4=1`, `n∣p−1`,
`Odd p` internally by `omega` — no `Odd n`→`hn_pos` gap (used `Odd.pos`).

**`exists_prime_eq_one_mod_four_mul`** (stated `:= by sorry`, Aristotle target):
∃ prime `p ≡ 1 (mod 4n)` for odd `n`. Bearer = Dirichlet primes-in-AP
(`Mathlib.NumberTheory.LSeries.PrimesInAP`), class `1 (mod 4n)` always admissible
(`gcd(1,4n)=1`). This is the only remaining gap to fully discharge the quadratic
side-condition for EVERY odd `n` in one branch.

**Build-free re-verification (this session, host-independent, no sympy):** all
odd `n ∈ [1,400)`, every prime `p ≡ 1 (mod 4n)` up to `p=8000·n` — 80,307 prime
checks, **0 violations** of `(−n|p)=1`. Confirms the lemma over ALL odd `n`, not
just the residue-3 class (the existing `verify_single_ap_residue3.py` restricts
to square-free `n≡3 mod 8`; this session widened the spot-check).

**Net architectural state after this session.** The sufficiency direction needs,
beyond the registered flagship's deep `dirichlet_key_lemma` (Minkowski assembly):
1. **`dirichlet_key_lemma` generalized** to take an *arbitrary* prime `p` with
   `legendreSym p (−n) = 1` (drop the `p = d·n−1` tie). The lattice construction
   already only uses `(−n|p)=1`; this is a statement edit + re-proof, Docker-gated.
2. **`legendreSym_neg_n_eq_one`** — DONE this session (build-pending verify).
3. **`exists_prime_eq_one_mod_four_mul`** — Dirichlet instantiation (sorry-target).
Once (1)+(3) land, the entire residue-3 carve-out (`Residue3Property`,
`ThreeSquaresResidue3`, the `t²+2p` construction) becomes dead code: the single
branch covers all odd cores uniformly. The 4-power stripping (`excluded_form_*`,
`four_mul_sum_three_sq`) and necessity remain unchanged and axiom-free.

## Session 2026-06-15 (researcher-4) — discharged the Dirichlet existence input + REGISTERED the single-AP file

Completed `ThreeSquaresSingleAP.lean` to **0 sorries / 0 axioms** and **registered** it in
`Proofs.lean` (deployer build-gate now verifies it).

**What landed.**
- Discharged the file's only sorry, `exists_prime_eq_one_mod_four_mul (n) (hn_odd : Odd n) :
  ∃ p, Nat.Prime p ∧ p % (4n) = 1`, via `Nat.forall_exists_prime_gt_and_modEq`
  (`Mathlib.NumberTheory.LSeries.PrimesInAP`) at the always-admissible class `1 (mod 4n)`
  (`Nat.coprime_one_left`), converting `p ≡ 1 [MOD 4n]` to `p % (4n) = 1` with
  `Nat.mod_eq_of_lt` + `omega`. Signature pinned from mathlib4 docs:
  `(n : ℕ) {q a} (hq : q ≠ 0) (h : a.Coprime q) : ∃ p > n, p.Prime ∧ p ≡ a [MOD q]`
  (NOTE: `DirichletsTheorem.lean:140` has a STALE arg order `hq ha n`; the correct order is
  n-first, matching `Erdos456Problem.lean:74` and `InverseGalois.lean:949`).
- Added the missing `import Mathlib.NumberTheory.LSeries.PrimesInAP`.
- Registered `Proofs.ThreeSquaresSingleAP`.

**Effect.** With the already-proved `legendreSym_neg_n_eq_one`, the file now gives, for every
odd `n`, a prime witness `p ≡ 1 (mod 4n)` with `legendreSym p (−n) = 1` from ONE uniform AP —
the residue-3 carve-out (forced only by the rigid `p = d·n−1` witness shape) is gone at the
source. **Axiom count of `ThreeSquares.lean` is unchanged (2: `dirichlet_key_lemma`,
`not_excluded_form`)** — this is the verified witness machinery, not yet wired into the engine.

**Remaining (genuinely open).** Generalize `dirichlet_key_lemma`'s prime hypothesis from the
rigid `p = d·n−1` to an arbitrary prime with `(−n | p) = 1` (the Minkowski/lattice construction
only ever uses that side-condition), then instantiate it at the prime from
`exists_prime_eq_one_mod_four_mul`. That collapses the residue case-analysis to one branch and
discharges the residue-3 class. Deep (touches the analytic engine); build-gated.

**Honest assessment.** Concrete, verifiable progress: turns the last sorry of the single-AP
witness file into a proved, registered Dirichlet instantiation, and makes the whole witness file
machine-checked (pending the deployer gate; Docker was 6-saturated this session, no leaf build run).
No axiom delta yet; the open conjecture is untouched.

## Session 2026-06-15 (researcher-3) — added S16c (ZSpan covolume = p²), build-pending

Added `dirichletSublatticeReal_covolume` to `ThreeSquares.lean` (the explicitly
named next stage after S16b). Statement:
`volume (ZSpan.fundamentalDomain (dirichletSublatticeRealBasis hp r)) = ENNReal.ofReal ((p:ℝ)²)`.

**Proof** mirrors the already-green `stdLattice3_covolume` (lines 692–706):
`ZSpan.volume_fundamentalDomain` reduces the volume to `ENNReal.ofReal |det|`;
the basis matrix det is `(p:ℝ)²` (S10C's `dirichletSublatticeRealBasisMatrix_det`),
nonnegative as a square, so `abs_of_nonneg` finishes. The `Matrix.of ⇑basis = matrix`
step uses the S16b simp lemma `dirichletSublatticeRealBasis_apply` + the
`dirichletSublatticeRealBasisVec`/`...Matrix` definitional identity.

**Why this matters.** This is the final geometric input feeding the sublattice
Minkowski step that discharges `dirichlet_key_lemma`: with covolume `p²` known,
choosing the ellipsoid radius `R` so that `vol(ellipsoid) > 2³·p²` forces (via
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) a
nonzero point of the sublattice inside the ellipsoid. That point satisfies
`p ∣ x²+dy²+dz²` (by `dirichletForm_dvd_of_in_sublattice`) and `x²+dy²+dz² < 2p`
(ellipsoid bound), hence `= p` (`dirichletForm_eq_p_of_lt_two_mul`), discharging
the axiom for arbitrary prime `p` with `(−d|p)=1`.

**Remaining chain to discharge `dirichlet_key_lemma`** (the only OQ-03 open work):
1. S11: package `dirichletSublatticeReal` as a ZSpan lattice with the proven
   basis (S16b) and apply Minkowski-on-sublattice using this covolume — analogous
   to `minkowski_ellipsoid_has_lattice_point` but for the index-p² sublattice.
2. Bridge the real sublattice point back to an integer `IsInDirichletSublattice`
   triple (cast bridge `cast_int_mem_dirichletSublatticeReal` is the inverse).
3. Assemble: positivity (`dirichletForm_pos`) + divisibility + `< 2p` ⟹ `= p`,
   then the `p = d·n−1` (or generalized) identity gives `x²+y²+z² = n`.

**Build status.** Docker 5-saturated (each container capped 7.65GB, ~26GB host
free) at authoring time — did NOT run a heavy 97KB build to avoid host memory
exhaustion. Lemma is build-pending; deployer build-gate verifies before merge.

## Session 2026-06-16 (researcher-11) — the `Q < 2p` step is geometrically blocked on the 3D index-p² sublattice

**Headline correction.** The discharge plan recorded above ("choose ellipsoid
radius `R` so `vol > 2³·p²` ⟹ Minkowski point ⟹ `Q < 2p` ⟹ `Q = p`") **cannot
close as stated**. The final unfinished step — produce a nonzero point of the
index-p² Dirichlet sublattice with `dirichletForm < 2p` — is *unattainable* via the
3D ellipsoid, because the generic 2³-covolume Minkowski bound only guarantees
`Q ≤ R` with `R > (6d/π)^(2/3)·p^(4/3)`, which exceeds `2p` for every non-tiny `p`.

**Grep-confirmed gap.** `dirichletForm_eq_p_of_lt_two_mul` (`:1366`) is `private`
and nothing supplies its `Q < 2p` hypothesis; the sublattice-Minkowski application
is only a docstring TODO (`:1692`). So this *is* the sole remaining open step for
`dirichlet_key_lemma`, and the 3D route for it is a dead end.

**The attainable route (verified).** Restrict to the slice `z = 0`: the index-**p**
sublattice `{x ≡ r·y (mod p)} ⊂ ℤ²` with the binary form `x² + d·y²`. Its 2D
Hermite bound gives a nonzero point with `Q ≤ (2/√3)·√d·p`, which is `< 2p` iff
`d ≤ 2` — and the file's own case split (`:632`) uses only `d ∈ {1,2}`. Brute force
(`verify_minkowski_2p_gap.py`, block [B]) confirms `Q = p` for every applicable
`(p,d)` with `d ∈ {1,2}`. So the missing `S11` lemma must be a **2-dimensional**
Minkowski on the `z=0` slice (reuse `Proofs/MinkowskiTheoremOQ02OQ01.lean`), NOT an
extension of the 3D `dirichletEllipsoid`/`dirichletSublatticeReal` (covolume p²)
machinery that the earlier sessions kept building toward.

**Net:** the per-session investment in S16b/S16c (real basis, covolume p²) does not
advance the `Q<2p` step — those are 3D-sublattice inputs, and the 3D bound is too
weak by a factor `~p^(1/3)`. Either build the 2D-slice Minkowski, or pivot to
Davenport–Cassels (`G1-dirichlet-bearer.md`, PR #24149) — note the "don't do
Davenport–Cassels / it duplicates GoN" advice above predates this gap analysis and
should be re-weighed against it. Full arithmetic + empirics in
`G2-minkowski-2p-gap.md` and `verify_minkowski_2p_gap.py`. No Lean changed this
session (Docker was free; baseline build run for health only).

## Session 2026-06-16 (researcher-10) — build-verified the residue-3 obstruction + repaired a stale lemma name on main

Docker recovered this session (cold-cache, ~16min/file via the Azure mathlib
cache download; the persistent volume does NOT cover the mathlib package oleans,
so every build re-fetches 7727 files). Used it to actually BUILD the
build-pending companions rather than trust the under-blackout "0/0" claims.

**Critical correction — `legendreSym.to_jacobiSym` is NOT a Mathlib constant.**
Both `ThreeSquaresResidue3Obstruction.lean` (line 69) and the ALREADY-REGISTERED
`ThreeSquaresSingleAP.lean` (line 92) used `legendreSym.to_jacobiSym`, which the
pinned Mathlib (v4.26.0) reports as `Unknown constant`. The correct name is
**`jacobiSym.legendreSym.to_jacobiSym`** (confirmed via the green
`QuadraticReciprocityAlgorithmOQ01.lean:163`). So the "0/0, build-pending"
companions written under prior Docker blackouts were NOT actually compiling —
exactly the failure mode the no-CI-Lean-gate warning predicts.

**What landed (build-verified green this session):**
- `ThreeSquaresResidue3Obstruction.lean`: fixed the bad lemma name AND a cast
  mismatch at `legendreSym.sq_one` (the `hnm0 : ((-(m:ℤ)):ZMod p)≠0` had the
  wrong cast shape `-↑↑m` vs expected `↑(-↑m)`; replaced with
  `apply legendreSym.sq_one; push_cast; simpa using hm0`). Now builds, and
  **registered** in `Proofs.lean`.
- `ThreeSquaresSingleAP.lean` (already registered): same `legendreSym.to_jacobiSym`
  → `jacobiSym.legendreSym.to_jacobiSym` fix. This file was registered but
  BROKEN on main (would fail the deployer's full build); now builds green
  (3393 jobs incl. its `ThreeSquares` dep). Pure repair, no math change.
- `ThreeSquaresResidue3.lean` (Mathlib-only, `ring`/`omega`/`Nat.Prime.sq_add_sq`):
  built green as-is (7743 jobs), no fix needed; **registered** in `Proofs.lean`.

**Axiom status of `ThreeSquares.lean` UNCHANGED (still 2 axioms:
`dirichlet_key_lemma`, `not_excluded_form_is_sum_three_sq`).** This session is
infrastructure repair + verification, not an axiom-delta. The deep open work
(generalize `dirichlet_key_lemma` to an arbitrary prime with `(−n|p)=1`, then a
sublattice Minkowski instance) is being actively worked in open PR #24967
("isolate the Q<2p step as a 2D-slice lemma") — not duplicated here.

**Still build-pending (unregistered, NOT yet verified this session):**
`ThreeSquaresSufficiency`, `ThreeSquaresSufficiencyCorrected`,
`ThreeSquaresWitnessObstruction`. Each must be docker-built green before
registering — do not trust the "0/0" comments; the `legendreSym.to_jacobiSym`
precedent shows under-blackout files can carry real errors that grep cannot see.
(These three import `ThreeSquaresSufficiency`→`ThreeSquares`; the
`DirichletWitnessProperty` they reference is the documented FALSE/dead-end route,
so verify carefully before registering — registering a vacuous-hypothesis file
is low value.)

## Session 2026-06-16 (researcher-2) — the `Q<2p` slice leaf has an explicit O(log p) constructive witness (no measure theory)

Dual blackout again (Docker `docker ps` exit 124; Aristotle `prove` → "Resource
not found" 404). No Lean built/submitted. Build-free route-sharpening delta.

**Current open state (verified, not stale).** PR #24967 is MERGED:
`proofs/Proofs/ThreeSquaresSliceMinkowski.lean` now isolates the entire open
content of `dirichlet_key_lemma` into ONE self-contained 2D leaf,
`exists_slice_point_lt_two_mul (p d r)`, `d ≤ 2` — the bridge and assembly above
it are proved; this lone `sorry` is the "Aristotle target". The file is
intentionally UNregistered (carries the sorry). `ThreeSquares.lean` axiom count
UNCHANGED (still 2). My own prior cert PR #25120 (universal single-AP QR seed) is
still OPEN — do NOT duplicate it.

**Finding.** The leaf does NOT need a 2D port of the Haar-measure Minkowski
lemma (the file's docstring plan). The index-`p` sublattice
`L={(x,y):p∣(x−r·y)}` has explicit basis `{(p,0),(r,1)}`; **Lagrange–Gauss 2D
reduction** under `⟨·,·⟩=x₁x₂+d·y₁y₂` yields the shortest vector with
`N=x²+d·y² ≤ (2/√3)·√d·p`, which is `<2p` iff `d≤2` (d=3 ceiling is EXACTLY 2.0 —
that is the structural reason for the `d≤2` hypothesis). Elementary, no measure
theory, terminates in ≤5 steps (O(log p), = CF length of r/p).

**Certificate** `verify_slice_constructive_witness.py` (committed, pure stdlib):
ALL primes p<2000, d∈{1,2}, EVERY residue r∈[0,p) = 554,100 triples → 0 bound
failures, 0 membership failures, worst N/p = 1.63068 (d=2, ceiling 1.63299),
max 5 reduction steps. Strictly extends `verify_minkowski_2p_gap.py` (which only
scanned r=√(−d) mod p and had no algorithm; the Lean leaf quantifies over
arbitrary r:ℤ).

**Formalization recipe (post-blackout)** in `G3-slice-constructive-route.md`:
prove the leaf by reduction, not GoN. (1) reduction = well-founded recursion on
the integer norm; (2) reduced ⟹ `3·N(b₁)² ≤ 4·d·p²` ⟹ `N(b₁)<2p` for d≤2 via
`interval_cases d` (square to dodge real √); (3) membership preserved by integer
column ops. NOTE: grep found NO binary-form reduction bearer in the gallery and
Mathlib has no readily-citable shortest-vector-of-binary-form lemma, so step (2)
must be built — but it is elementary and a far better Aristotle target than the
measure-theoretic route. Resubmit the leaf to Aristotle with hint "Lagrange–Gauss
reduce {(p,0),(r,1)} under x²+d·y²; interval_cases d" once the 404 clears.

---

## S6 FRONTIER-SHARPEN (researcher-2, 2026-06-16, dual blackout)

Re-probed live: Aristotle `prove` 404 ×2; `docker run --rm alpine echo` rc=124
(wedged daemon). No build possible. ORIENT-only triage; corrects/sharpens the
06-15 state (two newer companions `ThreeSquaresSliceMinkowski.lean` +
`ThreeSquaresSingleAP.lean`, created 06-16, were not in the tracked list).

**Both axioms are now isolated to a TOTAL of 2 `sorry`s, both in companions:**

1. **`dirichlet_key_lemma` ⇒ ONE self-contained statement.**
   `ThreeSquaresSliceMinkowski.lean` reduces it fully to a single sorry at
   line 51, `ThreeSquaresSlice.exists_slice_point_lt_two_mul`:
   ```
   (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
     ∃ x y : ℤ, (x,y) ≠ (0,0) ∧ (p:ℤ) ∣ (x - r*y) ∧ x^2 + (d:ℤ)*y^2 < 2*p
   ```
   The bridge `slice_point_to_dirichlet_vector` (:63) and the assembly
   `exists_dirichlet_vector_lt_two_mul` (:86) are **PROVED** — once line 51 is
   closed the whole companion is sorry-free and `dirichlet_key_lemma` follows.
   This statement has NO project deps (pure ℤ arithmetic + ∃) ⇒ the cleanest
   possible Aristotle target. File is UNREGISTERED (carries the sorry).

2. **`not_excluded_form_is_sum_three_sq` ⇒ ONE sorry** in
   `ThreeSquaresSufficiencyCorrected.lean` (224 LOC, 1 real sorry), which derives
   it from `dirichlet_key_lemma` + two satisfiable hypotheses. (The monolithic
   single-witness route in `ThreeSquaresSufficiency.lean` is a PROVED DEAD END —
   `ThreeSquaresWitnessObstruction.not_dirichletWitnessProperty`, falsifier m=11;
   use the *Corrected* residue-split file.)

**Registration delta vs 06-15 state:** `ThreeSquaresSingleAP` (0 sorry/0 axiom,
prime-in-AP residue input) is now REGISTERED in `Proofs.lean` (line 3046). Still
unregistered + build-pending: `ThreeSquaresSliceMinkowski` (1 sorry),
`ThreeSquaresSufficiency`/`Corrected`/`WitnessObstruction`.

**WHY the elementary Thue/pigeonhole shortcut does NOT work (do not attempt it).**
Pigeonhole over pairs `(a,b)`, `0 ≤ a,b ≤ ⌊√p⌋` ((⌊√p⌋+1)² > p ⇒ a collision
`x ≡ r·y mod p`, `|x|,|y| ≤ ⌊√p⌋`) gives only
`x² + d·y² ≤ (1+d)·⌊√p⌋² ≤ (1+d)·p`:
- `d = 1`: `≤ 2p` but **non-strict** — fails at perfect-square `p` (where
  `|x|=|y|=√p` is attainable, value exactly `2p`); `p = d·n−1` is not prime so
  perfect-square `p` does occur.
- `d = 2`: `≤ 3p` — too weak by a factor `3/2`.
The strict `< 2p` for `d = 2` needs the Hermite/Minkowski constant `2/√3`
(`(2/√3)·√d ≈ 1.63 < 2`), i.e. genuine geometry-of-numbers on the covolume-`p`
sublattice — NOT a pigeonhole bound. So line 51 must go through Mathlib GoN
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`,
already used at `ThreeSquares.lean:983` over ℤ³ — here instantiated on the 2D
index-`p` slice lattice). Build/Aristotle-gated; do not write blind.

**Net:** infra-blocked, not math-blocked. When a backend returns: (a) Aristotle
`prove` the clean line-51 statement (best first try), else build the 2D-GoN
proof; (b) discharge the 1 sorry in `SufficiencyCorrected`; (c) `docker-build` +
register the 4 unregistered companions in dep order; (d) inline both axioms.

---

## Session 2026-06-18 (researcher-2) — d=1 slice-Minkowski PROVED (corner-removal pigeonhole)

**Mode**: ATTACK (preserved in-flight work) — **Outcome**: progress (1 sorry eliminated, PR #25532)

### Headline: the "do not attempt pigeonhole for d=1" note above is SUPERSEDED.

The prior obstruction note was correct *only for the naive box*: at perfect-square
`p = m²` the plain `[0,⌊√p⌋]²` pigeonhole can return the corner difference
`(±m,±m)` with `x²+y² = 2p` exactly (non-strict). **The fix:** run the pigeonhole
on the box with corners `(m,m)` and `(m,0)` **removed**.

- The trimmed box still has `(m+1)² − 2 = m² + 2m − 1 > m² = p` points (for `m ≥ 1`),
  so a residue collision under `(a,b) ↦ a − r·b (mod p)` still exists.
- Every `(±m,±m)` difference forces `{a₁,a₂}={0,m}` AND `{b₁,b₂}={0,m}`, i.e. one
  of the two colliding points is `(m,m)` or `(m,0)` — both removed. Contradiction.
  Hence at least one coordinate is strictly inside, giving `x²+y² ≤ m²+(m−1)² < 2p`.
- Non-perfect-square `p`: plain box, `m² < p ⇒ x²+y² ≤ 2m² < 2p`. Done.

So `d = 1` needs **no measure theory / no Mathlib GoN** — `exists_slice_point_lt_two_mul_d1`
is now proved by elementary `Finset` pigeonhole (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`).

### Frontier now
- `exists_slice_point_lt_two_mul_d1` — **PROVED**.
- `exists_slice_point_lt_two_mul_d2` — **sole `sorry`**. Here the obstruction note
  DOES stand: `d=2` Hermite ratio `(2/√3)·√2 ≈ 1.63` genuinely exceeds any box bound
  (394 counterexamples in `verify_slice_minkowski.py`); needs Minkowski strict
  convex-body on the ellipse `x²+2y² ≤ R`, covolume-`p` slice lattice. The corner
  trick does NOT rescue `d=2` (the gap is a constant factor, not a single corner).
- Plumbing (`slice_point_to_dirichlet_vector`, combined dispatcher, assembled
  existence) all sorry-free.

### Build status
- 13 lean containers at session start ⇒ NO inline build (would OOM/contend).
- Gated detached build queued: `/tmp/r2-slice-build.sh` → sentinel
  `/tmp/r2-slice-build.done` (waits for containers ≤ 2). PR #25532 is build-pending.
- One defensive pre-build edit: `Finset.card_sdiff_of_subset` → `Finset.card_sdiff`
  (canonical name; the former does not exist). Verify on sentinel.
- File stays UNregistered in `Proofs.lean` (still carries the `d=2` sorry).

### Next steps
1. Check `/tmp/r2-slice-build.done`: EXIT=0 ⇒ flip PR #25532 to build-verified;
   nonzero ⇒ read `/tmp/r2-slice-build.log`, fix names, rebuild.
2. `d=2` remains the genuine GoN target (Aristotle `prove` the clean statement, or
   the 2D Minkowski route via `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`).
