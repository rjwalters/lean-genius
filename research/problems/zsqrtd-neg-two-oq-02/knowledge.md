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

## Session 2026-06-15 (S3, researcher-5) — GAP in PR #24443's DirichletWitnessProperty (n≡3 mod 8)

**Mode**: AUDIT + certify (build-free; Docker blackout). No `.lean` changed.

Open PR #24443 reduces the sufficiency axiom `not_excluded_form_is_sum_three_sq`
to a single `DirichletWitnessProperty` (∀ non-excluded m, 4∤m, m>1, ∃ d p,
p=d·m−1 prime, legendreSym p (−d)=1) and proposes discharging it via Dirichlet-AP
+ reciprocity. **That property is FALSE for n ≡ 3 (mod 8).**

Certified in `verify_dirichlet_witness.py`:
1. `legendreSym (d·n−1) (−d)` is a function of `(n%8, d%8)` (constant over all
   primes p=d·n−1 in range). +1 classes: n≡1,5→d≡2,6; n≡2,6→d≡1,2,5,6; **n≡3→NONE**.
2. Exhaustive (non-excluded, 4∤n, n<6000, d<200): the ONLY witness-less n are
   exactly the 750 values n≡3 mod 8 (every admissible even d gives −1). All are
   genuinely sums of three squares ⇒ real gap, not vacuous.
   ⇒ #24443's `three_sq_of_dirichlet_witness` is conditionally valid but its
   hypothesis is unsatisfiable for n≡3 mod 8, so it does NOT reduce the axiom; the
   proposed discharge is impossible as written. (ThreeSquares.lean:600 already
   treats n≡3 mod 8 separately — #24443 collapsed that distinction.)
3. Correct n≡3 route (certified, n<8000): ∃ odd t with (n−t²)/2 a sum of two
   squares a²+b² ⇒ n = t² + (a+b)² + (a−b)². (t²≡1 mod8 ⇒ (n−t²)/2≡1 mod4; pick it
   prime ≡1 mod4 via Dirichlet.) Uses Mathlib two-squares (`Nat.Prime.sq_add_sq`),
   NOT dirichlet_key_lemma.

**Fix for #24443**: split the witness property — require `n%8≠3` in
`DirichletWitnessProperty`, add the n≡3 two-squares branch to the reduction. Then
the (n≢3) witness via Dirichlet-AP+reciprocity is the genuine remaining ingredient;
the residue table gives the exact d%8 class to target per n%8.

### Files Touched (S3)
- `research/problems/zsqrtd-neg-two-oq-02/verify_dirichlet_witness.py`: new (certificate).
- `research/problems/zsqrtd-neg-two-oq-02/WITNESS-GAP-S3.md`: new (gap analysis + fix).
- `research/problems/zsqrtd-neg-two-oq-02/knowledge.md`: this entry.
- `research/problems/zsqrtd-neg-two-oq-02/state.md`: S3 focus.

## Session 2026-06-15 (S4, researcher-4) — S3's recommended fix is now IMPLEMENTED (PR #24628)

The S3 audit (above) found `DirichletWitnessProperty` (#24443) unsatisfiable for
n≡3 mod 8 and prescribed the fix: *"split the witness property — require n%8≠3 in
`DirichletWitnessProperty`, add the n≡3 two-squares branch to the reduction."*

**That fix is now implemented** in PR **#24628**,
`proofs/Proofs/ThreeSquaresSufficiencyCorrected.lean` (build-pending, unregistered
companion). It splits the open content into two SATISFIABLE hypotheses:

1. `DirichletWitnessNe3` — the Dirichlet witness restricted to m%8 ∈ {1,2,5,6}
   (exactly the +1 residue classes from S3's `verify_dirichlet_witness.py` table).
2. `Residue3Property` — for m%8=3, m>3: existence of a prime deficit mm=(m−t²)/2
   with mm%4≠3, consumed by `ThreeSquaresResidue3.three_sq_of_residue3_prime`
   (#24529, the Fermat two-square route S3 identified for n≡3 mod 8).

`three_sq_of_corrected_witnesses` proves full sufficiency from these two plus the
existing `dirichlet_key_lemma` axiom by strong-induction 4-power descent + mod-8
dispatch; the lone exceptional core n=3=1²+1²+1² (the only n≡3 mod 8 four-free
core with no prime deficit) is handled explicitly. 0 new axioms, 0 sorry.
`verify_corrected_split.py` (in the lagrange slug dir) re-certifies coverage and
the obstruction (m≤4000), corroborating S3's `verify_dirichlet_witness.py`.

**Remaining open work for this problem family** (Docker-gated, unchanged):
1. Discharge `DirichletWitnessNe3` via Dirichlet primes-in-AP + quadratic
   reciprocity on the four good residue classes (S3's residue table gives the
   exact d%8 target per n%8).
2. Discharge `Residue3Property` via Dirichlet primes-in-AP for the deficit.
3. Discharge `dirichlet_key_lemma` (the in-file Minkowski assembly).
Eliminating all three turns `ThreeSquares.lean`'s two axioms into a fully verified
three-square theorem. Do NOT re-derive the forward obstruction or the ℤ[√−2]
route (both complete); do NOT re-attempt the monolithic witness (proven false).

## Session 2026-06-15 (S5, researcher-4) — slim the residue-3 hypothesis + compile-audit

**Mode**: REVISIT · **Phase**: ACT · **Outcome**: additive Lean progress on the
unregistered companions (zero blast radius); Docker down (`docker info` timeout) →
build-pending. No registered file touched.

### Compile-correctness audit of the existing reduction (de-risk)

`ThreeSquaresResidue3.lean` + `ThreeSquaresSufficiencyCorrected.lean` (both on
`main`, build-pending, written under blackout) were name-checked vs the local
Mathlib clone and `ThreeSquares.lean`:
- `Nat.Prime.sq_add_sq {p} [Fact p.Prime] (hp : p%4≠3) : ∃ a b, a²+b²=p` — exact
  (`Mathlib/NumberTheory/SumTwoSquares.lean:35`).
- `Nat.strong_induction_on (n) (∀ n, (∀ m<n, p m) → p n) : p n` — exact
  (`Mathlib/Data/Nat/Init.lean:294`); `induction n using … with | _ n ih =>`
  auto-reverts `hne` into the motive, so `ih : ∀ m<n, ¬IsExcludedForm m → ∃…` and
  `ih m hmlt hmne` (Corrected:116) type-checks.
- `four_mul_sum_three_sq` → `…=(4*n:ℕ)`; `excluded_form_four_mul_iff :
  IsExcludedForm (4*n) ↔ IsExcludedForm n` — used with correct orientation;
  `ThreeSquares.lean` keeps all decls inside `namespace ThreeSquares`, reopened by
  the Corrected file, so unqualified refs resolve. Chain looks compile-correct
  (modulo a real build).

### New, verified-by-inspection content (this session)

`Residue3Property` carried an explicit `mm % 4 ≠ 3` clause; that clause is
**redundant** — for `m ≡ 3 (mod 8)` with an *odd* witness `t`, an odd square is
`≡ 1 (mod 8)`, so `2·mm = m − t² ≡ 2 (mod 8)`, forcing `mm ≡ 1 (mod 4)`.

Added (purely additive, no existing decl changed):
- `ThreeSquaresResidue3.residue3_deficit_one_mod_four` — `m%8=3 → Odd t →
  m=t²+2mm → mm%4=1` (odd-square-mod-8 via `Nat.even_mul_succ_self` + `omega`).
- `ThreeSquaresResidue3.three_sq_of_residue3_odd` — residue-3 route with `mm%4≠3`
  discharged internally; caller supplies only `Odd t` + prime deficit.
- `ThreeSquares.Residue3PropertyOdd` — slimmer open hypothesis (drops the side
  condition): `∀ m%8=3, 3<m, ∃ t mm, Odd t ∧ mm.Prime ∧ m=t²+2mm`.
- `ThreeSquares.Residue3Property_of_odd : Residue3PropertyOdd → Residue3Property`
  + `three_sq_of_corrected_witnesses_odd` (full sufficiency from
  `DirichletWitnessNe3` + `Residue3PropertyOdd`, reusing the existing induction).

**Net effect.** The residue-3 half of the sufficiency reduction now isolates a
*cleaner* open statement — just "∃ odd `t` with `(m−t²)/2` prime" (a thin-sequence
primality existence) — with the arithmetic mod-4 constraint dispatched. This does
NOT discharge the hypothesis (that primality is the genuine deep input); it removes
a spurious side-condition. Axiom budget unchanged. The deep open work in items 1–3
above is unchanged.

**Next session**: with Docker, build `Proofs.ThreeSquaresResidue3` +
`Proofs.ThreeSquaresSufficiencyCorrected`; remaining math = items 1–3 (all
Dirichlet/Minkowski-deep, not session-sized).
