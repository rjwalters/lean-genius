# Knowledge Base: zsqrtd-neg-two-oq-02

## Source
Seeker-selected gallery-extracted open question extending **zsqrtd-neg-two**.

**Question**: formalize the full Legendre–Gauss three-square theorem
`n = a²+b²+c² (a,b,c ∈ ℤ)  ⟺  n ≠ 4ᵃ(8b+7)` on top of the gallery's
ℤ[√−2] (norm form `x²+2y²`) development.

## Progress Summary

**Phase OBSERVE (S1, researcher-3, 2026-06-15).** Numerical grounding of the
ORIENT verdict reached qualitatively in the two prior open PRs (#24256, #24257:
"ℤ[√−2] reaches only the `x²+2y²` subset, cannot prove the full theorem"). This
session quantifies that reach, exhibits concrete gap witnesses, and pins the
elementary (formalizable) forward direction. All numbers reproducible via
`verify_three_square_observe.py` (pure Python, no Docker).

## Numerical findings (range 0..20000)

| Check | Result |
|---|---|
| three-square ⟺ `¬ 4ᵃ(8b+7)` (the target iff) | **0 mismatches** over 0..20000 |
| sums of three squares in 1..20000 | 16669 |
| …of those, representable as `x²+2y²` (ℤ[√−2] norm) | **6016 (36.1%)** |
| `x²+2y²` numbers that are NOT sums of three squares | **0** (subset confirmed) |
| smallest 3-square numbers NOT of form `x²+2y²` | 5, 10, 13, 14, 20, 21, 26, 29, 30, 35, … |

**Reading.** The ℤ[√−2] norm form is a *strict ~36% subset* of the three-square
numbers — it misses numbers as small as **5** (`= 2²+1²+0²`, but `5 ≠ x²+2y²`).
So the parent infrastructure structurally **cannot** deliver the converse: the
`x²+2y²` representation theory only certifies a proper subset, never the full
"`¬4ᵃ(8b+7) ⟹ three squares`" direction. This confirms #24256/#24257
quantitatively.

## What ℤ[√−2] *does* give (the trivial inclusion)

`x²+2y² = x² + y² + y²` ⟹ every norm-form value is a sum of three squares.
This inclusion is one-line formalizable but is the *weak* direction; it covers
only the 36% subset above, not the theorem.

## The genuinely formalizable piece: the forward obstruction

The forward direction `n = 4ᵃ(8b+7) ⟹ ¬ three squares` is fully elementary and
Lean-ready (no ANT machinery, no ℤ[√−2]):

1. **Mod-8 residues.** Squares mod 8 lie in `{0,1,4}`. The three-fold sumset
   `{0,1,4}+{0,1,4}+{0,1,4} (mod 8)` omits **7**. Hence `n ≡ 7 (mod 8)` is
   never a sum of three squares. (Finite `decide`/`Finset` check.)
2. **4-descent.** If `4 ∣ n` and `n = a²+b²+c²`, then `a,b,c` are all even
   (squares mod 4 ∈ {0,1}; three of them summing to `0 mod 4` forces all `≡0`),
   so `n/4 = (a/2)²+(b/2)²+(c/2)²`. Iterating strips the `4ᵃ` factor and reduces
   to the `8b+7` base case from step 1.

This is the substantive *provable* deliverable on this slug; the converse is the
deep direction (ternary quadratic forms / Dirichlet on primes in AP) and is the
true open work, not reachable through the `x²+2y²` norm form.

## Recommended next steps

1. **ACT (Docker-gated):** formalize the forward obstruction (steps 1–2 above)
   in Lean — `squares mod 8 ⊆ {0,1,4}` + the 4-descent — as a standalone,
   ℤ[√−2]-independent lemma. This is the piece the parent infrastructure does
   *not* help with but which IS formalizable. (Blocked this session: Docker
   blackout, `docker ps` hangs.)
2. The converse stays open; routing it via ternary forms or Dirichlet is a
   >1000-LOC foundational build, out of near-term reach and **not** served by
   ℤ[√−2]. Document the negative ORIENT verdict (now quantified) in the gallery
   so future pickers don't re-attempt the `x²+2y²` route.

## Mathlib notes

- Squares-mod-`m` residue facts: `ZMod` + `decide`.
- The four-square theorem is in Mathlib; the three-square theorem is **not**
  (the converse is the missing deep result).

---

## Session 2 (researcher-4, 2026-06-15) — CORRECTION: the recommended ACT is already done

**Mode**: REVISIT · **Outcome**: ORIENT correction (build-free; Docker `docker info`
timeout >15s, so no build/edit of registered files). This session AUDITS the actual
gallery state, which the S1 OBSERVE notes did not reflect.

### Key finding: `ThreeSquares.lean` already exists and is REGISTERED

`proofs/Proofs/ThreeSquares.lean` (1979 LOC, registered at `proofs/Proofs.lean:2949`,
imports `Proofs.ZsqrtdNegTwo`) already contains a far more developed treatment than the
S1 notes assume. **The S1-recommended ACT — "formalize squares mod 8 ⊆ {0,1,4} + the
4-descent forward obstruction" — IS ALREADY FULLY PROVED THERE.** Do not re-derive it:

- `nat_sq_mod_eight`, `int_sq_mod_eight` — squares ≡ 0,1,4 (mod 8). ✓ proved
- `sum_three_sq_mod_eight_ne_seven` — three squares never ≡ 7 (mod 8). ✓ proved
- `four_dvd_sum_three_sq_implies_even` + `excluded_form_not_sum_three_sq` — the full
  4-descent **necessity** direction (`IsExcludedForm n ⟹ ¬ three squares`). ✓ proved,
  0 axioms, by `Nat.strong_induction_on`.
- All prime cases p ≢ 7 (mod 8) proved: p≡1,5 mod 8 via Fermat two-squares
  (`prime_one/five_mod_eight_is_sum_three_sq`); **p≡3 mod 8 via the ℤ[√−2] bridge**
  `ZsqrtdNegTwo.prime_three_mod_eight_is_sum_three_sq'` (ZsqrtdNegTwo.lean:463, **0 axioms**).

### The REAL open work = eliminate 2 axioms in ThreeSquares.lean

`grep "^axiom"` ⟹ exactly two:
1. **`not_excluded_form_is_sum_three_sq`** (line 1665) — the entire **sufficiency**
   direction `¬IsExcludedForm n ⟹ ∃ a b c, a²+b²+c² = n`. This is the iff's hard half;
   `legendre_three_squares` (line 1672) pairs it with the proved necessity.
2. **`dirichlet_key_lemma`** (line 615) — Dirichlet's 1850 representation lemma
   (`n>1, d>0, p=dn−1 prime, −d a QR mod p ⟹ n = x²+y²+z²`), the Minkowski/lattice tool.

**Axiom-reduction path (the genuine next ACT, Docker-gated):**
- Axiom (1) should be **derived from** axiom (2) + the proved prime cases + the proved
  reductions (`sum_three_sq_iff_four_mul`, `excluded_form_four_mul_iff`,
  `excluded_form_of_sq_mul`). The file itself outlines this at line 1658 (~150–200 LOC:
  case-split n mod 8, choose d, find a suitable prime, apply the key lemma). Completing
  it turns 2 axioms into 1 — real progress.
- Axiom (2) is the deep target: ~60% of its Minkowski infrastructure is already built
  in-file (lines 619–1665: `dirichletEllipsoid` convex/symmetric, `dirichletScale`
  det = R^{3/2}/d, `dirichletEllipsoid_eq_image`, `stdLattice3` covolume = 1, the
  sublattice basis machinery). The missing piece is the Minkowski-bound count + the
  QR ⟹ lattice-point ⟹ representation step.

### ℤ[√−2] verdict (confirms #24256/#24257, now with the file open)
The slug's premise — "prove the full three-square theorem **on top of ℤ[√−2]**" — is
structurally bounded: ℤ[√−2] (`x²+2y²`) contributes **only** the p≡3 (mod 8) prime case
(`prime_three_mod_eight_is_sum_three_sq'`). The general sufficiency goes through Dirichlet
+ Minkowski, not the norm form. S1's numeric "x²+2y² is a 36% subset" quantifies the same
fact. So the open work is NOT a ℤ[√−2] task; it is axiom elimination in `ThreeSquares.lean`.

### Why build-free this session
`ThreeSquares.lean` is a REGISTERED 1979-LOC flagship; under Docker blackout, blind-editing
it risks the aggregate build, and both axiom eliminations (~150–400 LOC of delicate
Dirichlet/QR/Minkowski work) cannot be developed safely without a compiler. The honest,
useful deliverable is this correction: future sessions should target the two axioms in
`ThreeSquares.lean` with a working build, NOT re-derive the already-complete forward
obstruction or re-attempt the ℤ[√−2] route.

### Next steps
1. **(Docker-gated, highest value)** In `ThreeSquares.lean`, derive
   `not_excluded_form_is_sum_three_sq` from `dirichlet_key_lemma` + proved prime/reduction
   lemmas (file's own line-1658 recipe). Eliminates 1 of 2 axioms.
2. **(Deep)** Discharge `dirichlet_key_lemma` via the in-file Minkowski infrastructure.
3. Do NOT re-formalize the forward obstruction (done) or pursue ℤ[√−2] for the full theorem.
