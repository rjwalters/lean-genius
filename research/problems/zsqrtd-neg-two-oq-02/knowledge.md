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

## Session 2026-06-15 (S6, researcher-7) — CORRECTION: the companions have a real elaboration bug, not just "build-pending"

**Mode**: REVISIT · **Phase**: ORIENT · **Outcome**: documentary correction + turnkey
fix recipe (Docker contended at 4 lean-build containers on the 8 GiB VM → no safe
build; no registered file touched). This session CORRECTS the S4/S5 claim that the
sufficiency-reduction companions "check out by inspection, just build-pending."

### What's actually wrong (found via open PR #24887)

`ThreeSquares.lean` (registered) was **red on `main`** against Mathlib v4.26.0; the
fix is in flight as **PR #24887** (not this slug's deep math — two pre-existing
v4.26.0 tactic drifts, axiom budget unchanged at 2). While building the chain,
#24887 surfaced that the **unregistered** sufficiency companions do **not compile**:

- `ThreeSquaresSufficiency.lean:79` (`DirichletWitnessProperty`) and
- `ThreeSquaresSufficiencyCorrected.lean:65` (`DirichletWitnessNe3`)

both put `legendreSym p (-d : ℤ) = 1` *inside the witness `Prop`*:
`∃ d p : ℕ, 0 < d ∧ p = d*m-1 ∧ Nat.Prime p ∧ legendreSym p (-d : ℤ) = 1`.
`legendreSym (p) [Fact p.Prime] (a)` needs the `Fact (Nat.Prime p)` **instance** at
elaboration; the `Nat.Prime p` conjunct is a plain Prop term, NOT an instance, so
instance synthesis fails and the `def` does not elaborate. S4/S5's "checks out by
inspection" missed this because no build was ever run. **The companions cannot be
registered as-is.**

### Turnkey fix (apply with a free Docker, ≤2 containers)

State the QR condition in an **instance-free** form, then convert back at the one
consumer site. Both pieces already exist verbatim in the registered file:

1. **Statement** (both files): replace `legendreSym p (-d : ℤ) = 1` with
   `IsSquare ((-d : ℤ) : ZMod p)`. `IsSquare` over the `CommRing` `ZMod p` needs no
   `Fact`, so the `Prop` elaborates for any `p : ℕ`.
2. **Consumer** (`three_sq_of_corrected_witnesses`, Corrected:139–141; and the twin
   in `three_sq_of_dirichlet_witness`): after `haveI : Fact (Nat.Prime p) := ⟨hpp⟩`,
   recover `legendreSym p (-d) = 1` via
   `(legendreSym.eq_one_iff p hne0).mpr hqr` where
   `hne0 : ((-d : ℤ) : ZMod p) ≠ 0`. This `≠ 0` step + the `.eq_one_iff` conversion
   are **already proved in-file** at `ThreeSquares.lean:1191–1223`
   (`exists_int_sqrt_neg_d_mod_p`: `hd_zmod_ne` → `hneg_d_ne` → `legendreSym.eq_one_iff`).
   The `≠ 0` needs `¬ p ∣ d`, which is immediate from the witness shape:
   `p ∣ d ⟹ p ∣ d*m = p+1 ⟹ p ∣ 1`, contradicting `p` prime (`m ≥ 2`, so
   `d*m = (d*m-1)+1 = p+1`). No `0 < d < p` bound needed.

This is a ~15-line edit per file, zero new axioms/sorries, and unblocks registering
the corrected sufficiency reduction. It does **not** discharge any of the 3 deep
hypotheses (`DirichletWitnessNe3`, `Residue3PropertyOdd`, `dirichlet_key_lemma`) —
those remain the genuine open work (Dirichlet primes-in-AP + QR; in-file Minkowski).

### Aristotle / infra status (this session)
No Aristotle submission: the companions' blocker is an elaboration error, not a
`sorry`, and the 3 deep hypotheses are not single-`prove()` targets (large
Dirichlet/Minkowski assembly, not "known + no insight"). Docker contended (4
containers); registered-file fix owned by #24887. Order of operations for the next
Docker session: let #24887 land → apply the §"Turnkey fix" above → build & register
the corrected companions → then attack the deep hypotheses.

## Session 2026-06-16 (researcher-11) — CORRECTION to "the missing piece is just the Minkowski-bound count"

The repeated framing above (lines ~116–141: "discharge `dirichlet_key_lemma` via the
in-file Minkowski infrastructure / the missing piece is the Minkowski-bound count")
**understates the blocker**. Verified this session (on the sibling slug
`lagrange-four-squares-waring-g2-oq-03`, see its `G2-minkowski-2p-gap.md` +
`verify_minkowski_2p_gap.py`):

- `dirichlet_key_lemma`'s only unfinished step is producing a nonzero point of the
  **index-p²** Dirichlet sublattice with `dirichletForm < 2p` (feeds the proved
  `dirichletForm_eq_p_of_lt_two_mul`, which is `private` and whose `Q<2p` hypothesis
  NOTHING currently supplies — it is a docstring TODO).
- The in-file **3D ellipsoid** machinery (`dirichletEllipsoid`, `dirichletSublatticeReal`
  covolume p²) **cannot** supply `Q < 2p`: the generic 2³-covolume Minkowski bound needs
  `R > (6d/π)^(2/3)·p^(4/3)`, so it only yields `Q ≤ R ~ p^(4/3) ≫ 2p`. So "finish the
  Minkowski-bound count" on the existing 3D infrastructure does **not** close it.
- The attainable route is a **2D** Minkowski on the slice `z=0` (index-p sublattice of ℤ²,
  binary form `x²+dy²`, 2D Hermite bound `(2/√3)√d·p < 2p ⟺ d≤2`, covering the d∈{1,2}
  case split). Reuse `Proofs/MinkowskiTheoremOQ02OQ01.lean`. Or pivot to Davenport–Cassels.

**Net for this slug:** item "discharge `dirichlet_key_lemma`" should target a 2D-slice
Minkowski, not extend the 3D ellipsoid. The other open items (`DirichletWitnessNe3`, the
slimmed residue-3 primality, deriving `not_excluded_form` from the key lemma) are
unaffected and remain Docker-gated. Docker daemon was cold/unresponsive this session
(no companion build run).

## Session 2026-06-16 (S8, researcher-3) — verify registered SingleAP + single-AP architecture refinement

**Mode**: REVISIT · **Phase**: ORIENT/verify (build-free; DUAL BLACKOUT — Docker
builds blocked by corrupt `proofs/.lake` self-symlink `.lake -> .lake` "too many
levels of symbolic links" so Mathlib oleans unreachable; Aristotle MCP returns
`Resource not found` (404)). No registered `.lean` edited.

### 1. Build-free verification of the registered-but-uncompiled `ThreeSquaresSingleAP.lean`

`proofs/Proofs/ThreeSquaresSingleAP.lean` is committed on `origin/main` AND
registered (`Proofs.lean:3026`) but was **never compiled** (Docker pool saturated
when it landed). With NO CI Lean build gate, a single misnamed Mathlib bearer
would silently break `main`'s aggregate build for all agents. **All bearers
name-checked against the pinned Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(confirmed = local clone `/private/tmp/mathlib-grep` HEAD):**

| Bearer | Location (pin) | Sig OK |
|---|---|---|
| `jacobiSym.one_left (b:ℕ) : J(1\|b)=1` | JacobiSymbol.lean:148 | ✓ |
| `jacobiSym.mod_left' {a₁ a₂:ℤ}{b:ℕ}(h:a₁%b=a₂%b)` | JacobiSymbol.lean:225 | ✓ |
| `jacobiSym.quadratic_reciprocity_one_mod_four {a b:ℕ}(ha:a%4=1)(hb:Odd b):J(a\|b)=J(b\|a)` | JacobiSymbol.lean:425 | ✓ |
| `jacobiSym.neg (a:ℤ){b:ℕ}(hb:Odd b):J(-a\|b)=χ₄ b*J(a\|b)` (protected) | JacobiSymbol.lean:319 | ✓ |
| `legendreSym.to_jacobiSym (p:ℕ)[Fact p.Prime](a:ℤ)` | JacobiSymbol.lean:115 | ✓ |
| `ZMod.χ₄_nat_one_mod_four {n:ℕ}(hn:n%4=1):χ₄ n=1` (in `namespace ZMod`) | ZModChar.lean:89 | ✓ |
| `Nat.forall_exists_prime_gt_and_modEq (n:ℕ){q a:ℕ}(hq:q≠0)(h:a.Coprime q)` (in `namespace Nat`) | PrimesInAP.lean:508 | ✓ |
| `Nat.coprime_one_left` | used Mathlib-wide (Totient.lean:279, Rat/Lemmas.lean:306) | ✓ |

The Jacobi/reciprocity rewrite chain in `legendreSym_neg_n_eq_one` (lines 92–96)
type-checks by inspection: `to_jacobiSym` ⟶ `jacobiSym.neg` gives
`χ₄ p * J(n|p) = 1`; `χ₄_nat_one_mod_four hp4` + `one_mul` ⟶ `J(n|p)=1`;
`← quadratic_reciprocity_one_mod_four hp4 hn_odd` ⟶ `J(p|n)=1` = `hJpn`. Residual
risk is purely tactic-level elaboration (coercion unification / `omega`), NOT
missing or misnamed lemmas. **The registered-on-main risk is cleared.**

### 2. SingleAP makes the residue-3 carve-out OBSOLETE for ODD cores

`ThreeSquaresSingleAP` provides a UNIFORM witness for every **odd** `n`:
`exists_prime_eq_one_mod_four_mul` (a prime `p ≡ 1 mod 4n`) +
`legendreSym_neg_n_eq_one` (`legendreSym p (-n)=1`). This single arithmetic
progression covers `n % 8 ∈ {1,3,5}` in one branch — including `n ≡ 3 (mod 8)`,
the exact class whose old rigid `p = d·n−1` witness was proven UNSATISFIABLE
(`ThreeSquaresResidue3Obstruction.no_residue3_witness`) and which forced the
entire `ThreeSquaresResidue3*` / `Residue3Property` carve-out in
`ThreeSquaresSufficiencyCorrected`.

**Numeric certificate** `verify_single_ap_coverage.py` (range 1..4000):
- 2000 odd n: `legendreSym(p,-n)=1` for smallest prime `p≡1 mod 4n` — **0 mismatches**, **0 existence failures**.
- non-excluded 4-free cores: **1499 ODD** (single-AP covers) vs **1000 EVEN** (`n%8∈{2,6}`, NOT covered).

### 3. The GAP: even cores (`n % 8 ∈ {2,6}`) are NOT served by single-AP

`legendreSym_neg_n_eq_one` requires `Odd n` (the Jacobi bottom must be odd for
`jacobiSym.neg` / `quadratic_reciprocity_one_mod_four`). The descent in
`three_sq_of_corrected_witnesses` strips only **fours** (`4∣n → n/4`), so the
4-free core can be even (`≡ 2 mod 4`). The old `DirichletWitnessNe3` covered
`m%8∈{1,2,5,6}` — the even classes 2,6 included. SingleAP does **not** replace
those. So single-AP shrinks but does not eliminate the open witness content.

### 4. Turnkey wiring plan (next backend-up session)

To convert axiom `not_excluded_form_is_sum_three_sq` (ThreeSquares.lean:1720)
into a theorem (2 axioms → 1) using SingleAP:

1. **Restate** `dirichlet_key_lemma` (ThreeSquares.lean:648) to the relaxed,
   tie-free witness form — drop `d`, `hd`, `hp : p=d·n−1`; change the QR side
   condition to `legendreSym p (-(n:ℤ)) = 1`:
   ```
   axiom dirichlet_key_lemma {n p : ℕ} (hn : n > 1) [Fact (Nat.Prime p)]
       (hqr : legendreSym p (-(n:ℤ)) = 1) : ∃ x y z : ℤ, x^2+y^2+z^2 = n
   ```
   (The Minkowski/lattice construction only needs `-n` a QR mod some prime `p`;
   the rigid tie was never essential. Still TRUE — single-AP supplies arbitrarily
   large such `p` — so the eventual Minkowski discharge stays possible.)
2. **Odd cores** (`n%8∈{1,3,5}`): discharge directly via
   `exists_prime_eq_one_mod_four_mul` + `legendreSym_neg_n_eq_one` + restated
   `dirichlet_key_lemma`. DELETE the `n%8=3` branch and the entire
   `ThreeSquaresResidue3` / `ThreeSquaresResidue3Obstruction` /
   `ThreeSquaresWitnessObstruction` / `Residue3Property*` machinery.
3. **Even cores** (`n%8∈{2,6}`): still need a witness. Either keep a
   `DirichletWitnessNe3` restricted to even cores, OR find a 2-descent
   (`n = 2m`, `m` odd) — open which is cleaner; flag as the residual sub-task.
4. Net if wired: `ThreeSquares.lean` drops to **1 axiom** (relaxed Minkowski
   `dirichlet_key_lemma`) + the small even-core witness; the residue-3 obstruction
   apparatus is removed entirely.

**Do NOT** under blackout: blind-restate the axiom / blind-write the wiring in the
registered flagship (no compiler to catch elaboration). **Do NOT** re-chase the
monolithic `DirichletWitnessProperty` (proven false) or the ℤ[√−2] route (a 36%
subset, structurally insufficient).

### Files touched (S8)
- `verify_single_ap_coverage.py` — new (single-AP QR + coverage certificate).
- `knowledge.md` / `state.md` — this entry.

## Session 2026-06-16 (S10, researcher-2) — even-core residual: thin-prime trick FAILS; correction to S8

**Mode**: REVISIT · **Phase**: ORIENT/certify (build-free; DUAL BLACKOUT confirmed
this session — `docker version` rc=124 timeout, daemon hung; `proofs/.lake` is the
self-referential symlink loop `proofs/.lake -> proofs/.lake` ⇒ "Too many levels of
symbolic links" ⇒ Mathlib oleans unreachable even if Docker came up). No `.lean`
edited. Aristotle not applicable (the residual is a reduction-design question, not a
single `sorry` target).

### What S8 left open, and what this session settles

S8 reduced the sufficiency picture to: ODD 4-free cores discharged via
`ThreeSquaresSingleAP` (prime `p ≡ 1 mod 4n` ⇒ `legendreSym(p,−n)=1`), leaving the
**EVEN 4-free cores** `n%8 ∈ {2,6}` (`4∤n`) as the sole residual, with the open
question *"keep a Dirichlet witness restricted to even cores, OR find a 2-descent —
which is cleaner?"*. The tempting clean option is to transplant the residue-3
**thin-prime** trick (odd `t`, `(m−t²)/2` prime ⇒ Fermat two-squares) to even cores
using **even** `t`.

**That transplant is FALSE.** Certified in `verify_even_core_witness.py`
(`n%4==2`, `2<n≤10⁶`, 249999 cores):

- Parity: a three-square rep of `n≡2 mod4` uses exactly two ODD squares + one EVEN
  square `t`, so `n − t² = (odd)²+(odd)² = 2s`, `s=(n−t²)/2` odd, and
  `s=c²+d² ⟺ n = t² + (c+d)² + (c−d)²`. So an even-core witness ⟺ **even `t` with
  `(n−t²)/2` a sum of two squares.**
- **STRICT** ("`s` prime, `s%4=1`" — the residue-3-style reduction): **45 sporadic
  failures**, members as large as **68566** within 10⁶:
  `{6,18,22,54,66,102,114,130,166,190,286,306,354,438,454,478,534,646,666,694,766,
  826,994,2146,…,36670,68566}`. E.g. `n=22`: even `t∈{0,2,4}` give `s∈{11,9,3}`;
  `11,3` are primes `≡3 mod4`, `9` is composite — yet `9=3²+0²` so `22=2²+3²+3²`.
  ⇒ the thin-prime trick does **not** transplant to even cores.
- **BROAD** ("`s` a sum of two squares" — the true characterization): **0 failures**,
  identity `n=t²+(c+d)²+(c−d)²` exact (0 failures), max even `t` needed = 96. But
  "∃ even `t` with `(n−t²)/2` a sum of two squares" is a **reformulation of the goal**
  (n is three squares with an even coordinate), NOT a reduction to a
  Dirichlet-dischargeable statement.

### Correction to S8 and refined wiring plan

- **S8's "even-core thin-prime might be cleaner" is wrong.** There is no clean
  thin-prime even-core lemma; a future Docker session should NOT attempt one.
- Even cores must go through the **general QR/Minkowski route**: the relaxed
  `dirichlet_key_lemma` `(hqr : legendreSym p (−(n:ℤ)) = 1) ⇒ ∃ x y z, x²+y²+z²=n`
  (S8 §"Turnkey wiring", which does NOT require `Odd n` — `legendreSym p a` is fine
  for even residue `a`). The ONLY even-specific work is the **prime finder**:
  `ThreeSquaresSingleAP.legendreSym_neg_n_eq_one` needs `Odd n` for the Jacobi
  reciprocity step, so for even `n=2m` (`m` odd) split `−n = −2m` and choose `p`'s
  residue class mod `8m` so that `legendreSym p (−2)·legendreSym p m = +1` (the
  `χ₈`/`χ₄` supplementary laws + reciprocity on the odd part `m`). Then Dirichlet-AP
  supplies the prime. This is an **extension** of SingleAP for the factor of 2, not a
  Fermat shortcut.
- Net unchanged deep work (Docker-gated): (1) land the S6 elaboration fix
  (`IsSquare ((−d:ℤ):ZMod p)` form) + build/register the corrected companions;
  (2) generalize the SingleAP prime finder to even `n` per the split above;
  (3) discharge the relaxed `dirichlet_key_lemma` via a **2D-slice** Minkowski
  (S "researcher-11" note: the 3D ellipsoid cannot reach `Q<2p`).

### Files touched (S9)
- `research/problems/zsqrtd-neg-two-oq-02/verify_even_core_witness.py` — new
  (STRICT-fails-sporadically + BROAD-always-holds + identity certificate).
- `knowledge.md` / `state.md` — this entry.

## S11 — 2D-slice Minkowski lemma certified true; d=1/d=2 route split (researcher-4, 2026-06-17)

**Mode**: REVISIT · **Phase**: ORIENT/certify (build-free). Docker daemon responsive
(`docker info` rc=0) but worktree == `origin/main` HEAD (already S9-GREEN, no rebuild
value); **Aristotle still 404** ("Resource not found") so the isolated `sorry` cannot
be auto-proved this session. No `.lean` edited.

### What this settles

The whole development now has exactly ONE open `sorry`:
`exists_slice_point_lt_two_mul` in `Proofs/ThreeSquaresSliceMinkowski.lean:47` (its
bridge `slice_point_to_dirichlet_vector` is proved). It is the 2D geometry-of-numbers
input to `dirichlet_key_lemma` (`ThreeSquares.lean:648`, an axiom). This session
certifies the lemma is TRUE and pins the formalization route.

Certificate `verify_slice_minkowski.py` (exhaustive integer search):

| check | result |
|-------|--------|
| min over `L_{p,r}` of `x²+d·y² < 2p`, `p∈[1,1200]`, all `r`, `d∈{1,2}` | **0 failures** |
| worst `min/p`, d=1 | `1.15311` (p=209,r=56) vs Hermite cap `2/√3 = 1.15470` |
| worst `min/p`, d=2 | `1.63207` (p=1079,r=484) vs Hermite cap `2√2/√3 = 1.63299` |
| Thue box `\|x\|,\|y\|≤⌊√p⌋` suffices? d=1 | YES (0 box-failures, `p≤400`) |
| Thue box suffices? d=2 | **NO** — `394` `(p,r)` cases with box-best `≥ 2p` |

### Consequences for the Lean proof

- The `< 2p` target is exactly right: the worst case approaches the binary Hermite
  constant `2/√3·√d` (< 2 for `d≤2`) but never reaches 2 ⇒ use the **strict-`<`**
  Minkowski convex-body theorem `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
  (`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean:65`), not the `≤` compact one.
- **Split the lemma by `d`**:
  - `d=1`: elementary — a Thue/pigeonhole point with `|x|,|y|≤⌊√p⌋` already gives
    `x²+y²≤2p`, strict on a nonzero non-corner point. No measure theory. (Mathlib has
    no standalone Thue lemma; pattern is inlined at `SumFourSquares.lean:61`.)
  - `d=2`: the box bound is only `≤3p` and provably insufficient (394 counterexamples)
    ⇒ MUST use the disk area bound `area{x²+2y²≤R}=πR/√2`, Minkowski on the covolume-`p`
    sublattice with `R∈(4p√2/π, 2p)` (nonempty iff `4√2/π≈1.80<2`). No binary-form
    Hermite-reduction API exists at the pin, so the measure-theoretic route is forced.

### Net open work (unchanged, Docker+Aristotle-gated)

(1) S6 elaboration fix + register corrected companions; (2) generalize the SingleAP
prime finder to even cores (S10); (3) discharge `exists_slice_point_lt_two_mul` per
the d=1/d=2 split above ⇒ `dirichlet_key_lemma` axiom→theorem (`ThreeSquares.lean`
2 axioms → 1). Item (3) is now the most sharply specified of the three.

### Files touched (S11)
- `research/problems/zsqrtd-neg-two-oq-02/verify_slice_minkowski.py` — new.
- `knowledge.md` / `state.md` — this entry.

## Session 2026-06-18 (researcher-12) - d=2 slice-Minkowski turnkey recipe

**Mode**: REVISIT (claimed via claim-random; RICH tier)
**Outcome**: progress (ORIENT/ACT — recipe pinned; no verified Lean: build + Aristotle both gated)

### What I Did
- Located the live route: `Proofs/ThreeSquaresSliceMinkowski.lean`, whose SOLE code
  `sorry` is `exists_slice_point_lt_two_mul_d2` (d=2: nonzero point of the index-p
  sublattice `{(x,y): p|(x-ry)}` with `x²+2y² < 2p`).
- Tried to delegate it to Aristotle (it is a textbook HARD/known-math sorry, not OPEN):
  the Aristotle MCP backend returned `Resource not found` for every `prove` call
  (async, sync, and a trivial smoke test) — backend is DOWN this session.
- Re-verified numerically: target lemma TRUE for all p<1500, all r (0 counterexamples).
- Ruled out elementary shortcuts: box pigeonhole min is `2√2·p > 2p`; the strict
  small-ellipse count `#{x²+2y²<p/2} > p` fails for many p. Minkowski genuinely needed.
- Found the decisive simplification by reading the proved axiom-free
  `dirichlet_approximation` (`MinkowskiTheoremOQ02OQ01.lean:161`): keep the STANDARD
  `ℤ²` lattice and shear the SET. With `S=!![p,r;0,1]` (det p) and
  `E' = S⁻¹(ellipse {x²+2y²<2p})`, `vol(E') = √2·π·p / p = √2·π ≈ 4.443 > 4`,
  **p-INDEPENDENT** — Minkowski applies uniformly. The returned integer `(a,b)` gives
  `(x,y)=(a·p+b·r,b)` with `p|(x−ry)=a·p` automatic. Validated for all p<400.

### Key Findings
- d=2 reduces to a near-verbatim port of `dirichlet_approximation`; only new ingredient
  is the 2D ellipse volume `√2·π·p` (port `dirichletEllipsoid_volume` from 3D→2D) plus
  the `Measure.map S` change of variables (as in `dirichletSet_volume`).
- The covolume-p custom-sublattice framing in the old docstring is avoidable — the
  shear-the-set framing is strictly simpler (covolume stays 1, margin is constant).

### Files Modified
- proofs/Proofs/ThreeSquaresSliceMinkowski.lean (enhanced d=2 docstring + STATUS block
  with the turnkey recipe; code unchanged — still one clean `sorry`)
- src/data/research/problems/zsqrtd-neg-two-oq-02.json (insights/nextSteps/progress)

### Next Steps
- Build-capable session: execute the recipe (≈ copy `dirichlet_approximation`). 
- Or submit `exists_slice_point_lt_two_mul_d2` to Aristotle once its backend recovers.

## Session 2026-06-19 (researcher-1) — factor the arithmetic glue out of the d=2 Minkowski sorry

**Mode**: REVISIT (claim-random, RICH) · **Phase**: ACT · **Outcome**: additive,
hand-verified Lean progress on the UNREGISTERED `ThreeSquaresSliceMinkowski.lean`
(zero blast radius); both backends DOWN this session — Docker `docker info` rc=124
(daemon hung, host OOM-saturated), Aristotle MCP `prove` returns `Resource not
found` (404, probed with the isolated d=2 lemma). No build, no registered file
touched.

### What I did

The development still has exactly ONE code `sorry`. Prior sessions left it as the
*whole* statement `exists_slice_point_lt_two_mul_d2` (slice point existence). I
**factored it** into:

- `slice_point_of_sheared_d2` (**PROVED**, pure `ring`/`omega`/`mul_eq_zero`): given
  a nonzero `(a,b)` with the *sheared* form `(a·p+b·r)² + 2b² < 2p`, produce the
  slice point `(x,y)=(a·p+b·r, b)`. Discharges all three plumbing obligations —
  `p ∣ (x−r·y)=a·p` via `⟨a, by ring⟩`; `(x,y)≠(0,0)` from `(a,b)≠0 ∧ p>0` (if
  `b=0` then `x=a·p≠0`); and `x²+2y²<2p` verbatim from the hypothesis.
- `exists_sheared_point_lt_two_mul_d2` (**OPEN, the new sole sorry**): the tight,
  purely-geometric core — `ℤ²` has a nonzero point in the sheared open ellipse. This
  is exactly the input to Minkowski's strict convex-body theorem, `vol = √2·π > 4`
  (p-independent). This is what a build/Aristotle session must discharge.
- `exists_slice_point_lt_two_mul_d2` is now **PROVED** by `obtain … := core; exact
  slice_point_of_sheared_d2 …`.

### Why this (and not the full port)

Writing the ~80-line measure-theory port blind is the exact anti-pattern S6
documented (the `Fact`-instance elaboration bug that "checks out by inspection"
missed). Under dual blackout the honest deliverable is the mechanical, hand-verifiable
glue, which (a) isolates the irreducible geometry into a sharper statement, (b)
pre-verifies the arithmetic so the eventual build session only needs the Minkowski
core, and (c) cannot break the deployer build (file unregistered). Sorry count
unchanged at 1 (no new sorries); the open content is strictly smaller.

### Net open work (unchanged, backend-gated)
1. Discharge `exists_sheared_point_lt_two_mul_d2` via the turnkey shear-the-set
   recipe (now the sole sorry) ⇒ `dirichlet_key_lemma` axiom→theorem.
2. SingleAP prime finder for even cores (S10); land the S6 `IsSquare`-form
   elaboration fix on the sufficiency companions.
3. Both 1–2 require a working Docker or a recovered Aristotle backend.

### Files touched
- `proofs/Proofs/ThreeSquaresSliceMinkowski.lean` — +`slice_point_of_sheared_d2`
  (proved), +`exists_sheared_point_lt_two_mul_d2` (sorry), rewired d=2 slice theorem,
  refreshed header/docstrings.
- `knowledge.md` / `state.md` — this entry.
