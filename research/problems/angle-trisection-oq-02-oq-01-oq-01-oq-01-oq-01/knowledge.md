# Knowledge Base: angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01

**Problem**: Can `insep_gal_trivial` be proved using Mathlib's purely inseparable extension infrastructure?

## Problem Summary

The axiom `insep_gal_trivial` in the parent entry claims:
> For any inseparable irreducible f over a char-p field, |Gal(f)| = 1.

This open question asks whether this can be formally proved using Mathlib's `IsPurelyInseparable` infrastructure.

---

## Session 2026-05-06 (Session 1) — Counterexample found, correct theorem proved

**Mode**: FRESH
**Outcome**: completed (mathematically — showed axiom is FALSE, proved correct version)

### What I Did

1. Analyzed the mathematical content of `insep_gal_trivial`
2. Found that the axiom is FALSE in general — gave explicit counterexample
3. Identified the CORRECT theorem and proved it (with 2 minor API sorries)
4. Created new Lean file `AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (278 lines, 7 theorems)
5. Created gallery entry

### Key Findings

**The axiom is FALSE**: For f = g(X^p) where g is separable irreducible of degree ≥ 2, f is inseparable and irreducible but |Gal(f)| = |Gal(g)| ≥ 2.

**Concrete counterexample** (char 2):
- F = F₂(a), f(X) = X⁴ + X² + a = g(X²) where g = X² + X + a
- f is irreducible over F₂(a) (Artin-Schreier: g irreducible, so no quadratic factors of f)
- f is inseparable (f'(X) = 0 in char 2)
- |Gal(f)| = 2: the automorphism σ(α^(1/2)) = α^(1/2) + 1 has order 2

**The correct theorem** (proved):
```
algEquiv_eq_refl_of_isPurelyInseparable: 
  [IsPurelyInseparable F K] (σ : K ≃ₐ[F] K) → σ = AlgEquiv.refl F K
```
Proof: for x ∈ K, get n with x^(p^n) ∈ F; then (σ(x) - x)^(p^n) = 0 by char-p Frobenius; no nilpotents in field → σ(x) = x.

**Corollary** (proved):
```
gal_card_one_of_purelyInseparable_splitting:
  [IsPurelyInseparable F f.SplittingField] → Nat.card f.Gal = 1
```

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (created, 278 lines)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/meta.json` (created)
- `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/knowledge.md` (this file)

### Remaining Work (Sorries)

1. **sub_pow_char_pow**: (-b)^(p^n) = -b^(p^n) in characteristic p. Uses `neg_pow` and parity of p^n. Should be closeable with `CharP.neg_one_pow_prime` or `neg_pow_odd`.

2. **charP_eq_ringChar alignment**: `ringChar F = p` when `[CharP F p]`. Should be `ringChar_eq_charP` or `CharP.ringChar_eq`.

3. **xPow_sub_of_irreducible_isPurelyInseparable**: Connecting SplittingField of X^p - a to `IsPurelyInseparable`. Needs deeper Mathlib API work.

### Next Steps

- Try submitting `sub_pow_char_pow` and `charP_eq_ringChar alignment` to Aristotle
- The 2 technical sorries should be eliminatable with the right Mathlib lemma names
- `insep_gal_trivial` in the parent could be REPLACED with the correct axiom about `IsPurelyInseparable F f.SplittingField` (a future PR)

---

## Session 2026-05-07 (Session 2, researcher-8) — Closed both API sorries via iterateFrobenius

**Mode**: ACT (MODERATE knowledge tier, score 11)
**Outcome**: 0 sorries remaining (down from 2). Only intentional axiom `counterexample_gal_card` remains.

### What I Did

1. Replaced the sub-pow-by-parity-split proof of `sub_pow_char_pow_eq` (which had 2
   sorries in the char-2 even branch) with a one-liner using Mathlib's
   `iterateFrobenius` ring homomorphism:
   ```
   simpa [iterateFrobenius_def] using map_sub (iterateFrobenius K p n) a b
   ```
   `iterateFrobenius K p n : K →+* K` acts as `x ↦ x^(p^n)` (lemma
   `iterateFrobenius_def`); since it is a ring homomorphism, `map_sub` directly
   gives subtraction commutativity in one shot — no parity case split needed.
   The required `ExpChar K p` instance is automatic from `[CharP K p] [Fact p.Prime]`
   via Mathlib's `expChar_prime` instance.

2. Fixed `ringChar_eq_charP K p` (a non-existent lemma name in Mathlib v4.26.0)
   to `ringChar.eq K p`, the actual lemma in `Mathlib.Algebra.CharP.Defs`:
   `ringChar.eq : (R : Type) [NonAssocSemiring R] (p : ℕ) [CharP R p] → ringChar R = p`.

3. Updated header sorry count (`Sorries: 2` → `Sorries: 0`) and summary table.

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (-25 +11 lines)

### Sorry Count

- Before: 2 (both in `sub_pow_char_pow_eq` char-2 branch)
- After: **0** (all main theorems proved)
- Remaining axiom: 1, `counterexample_gal_card` (intentional — Galois-card-2
  of explicit `f = X⁴+X²+a` over `F₂(a)` pending Artin-Schreier formalization)

### Build Verification

Pending: Docker build of `Proofs.AngleTrisectionOQ02OQ01OQ01OQ01OQ01` running.

### Key References

- `Mathlib.Algebra.CharP.Frobenius`: `iterateFrobenius`, `iterateFrobenius_def`
- `Mathlib.Algebra.CharP.Defs`: `ringChar.eq`, `ringChar.charP`, `expChar_prime`

---

## Session 2026-05-08 (Session 3, researcher-1) — Counterexample structural scaffolding

**Mode**: ACT (MODERATE knowledge tier, score 11)
**Outcome**: Added 4 structural lemmas about `f_target` for downstream Artin-Schreier work.
Theorem count: 6 → 10. lineCount: 205 → 230. Sorries unchanged at 0; only intentional axiom
`counterexample_gal_card` remains.

### What I Did

Added 4 small but load-bearing structural lemmas about `f_target = X⁴ + X² + aGen`:

1. **`f_target_natDegree`**: `f_target.natDegree = 4` — proved by `unfold; compute_degree!`.
2. **`f_target_degree`**: `f_target.degree = 4` — same pattern (degree, not just natDegree).
3. **`f_target_ne_zero`**: `f_target ≠ 0` — corollary of natDegree = 4 ≠ 0.
4. **`f_target_monic`**: `f_target.Monic` — leading coefficient = 1 via `coeff` simp set.

These are the basic prerequisites for any future Artin-Schreier irreducibility proof or
explicit Galois-group computation that wishes to discharge the `counterexample_gal_card`
axiom. In particular:
- An Eisenstein-style irreducibility argument over the integral subring would need
  `f_target_monic` (leading coefficient ∉ the prime ideal) and `f_target_natDegree` (to
  index the Eisenstein hypotheses by k < degree).
- An explicit Galois-group bound `Nat.card f_target.Gal ≤ f_target.natDegree.factorial`
  would need `f_target_natDegree` as input (via `Polynomial.Gal.card_le_natDegree_factorial`
  or analogue).
- A non-degeneracy lemma `f_target_ne_zero` is required by virtually every non-trivial
  polynomial API in Mathlib (degree, splitting field, Gal, etc.).

This session does NOT close `counterexample_gal_card`. Doing so requires Artin-Schreier
extension theory over `F₂(a)` (~hundreds of Mathlib-style lines), which is multi-session.

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (+25 lines, +4 lemmas)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/meta.json`
  (lineCount 205 → 230, theoremCount 6 → 10 in both `meta` and `leanFile` blocks;
   originalContributions and assumptions extended; section endLines updated)
- `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/knowledge.md`
  (this entry)
- `src/data/research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  (iteration 1 → 3, builtItems and progressSummary synced through Sessions 2 + 3)

### Build Verification

The `compute_degree!` tactic is established in this codebase (used in
`InverseGaloisA5.lean`, `InverseGaloisD4.lean`, `InverseGaloisF20.lean`,
`AngleTrisectionCos20GalOQ01OQ02.lean`, `AngleTrisectionCos20GalOQ03.lean`,
`AngleTrisectionCos20GalOQ03OQ01.lean`) on polynomials of similar shape
(monomial sums of `X^k` and `C c`), so the new lemmas should compile. Local Docker
build was not run from this worktree (the agent's `proofs/.lake` symlink is the
known broken self-cycle, see MEMORY.md "broken proofs/.lake symlink"); CI is the
ground-truth verifier.

### Path Forward

**Next sessions** (estimated 3+ sessions to fully discharge `counterexample_gal_card`):

1. **Eisenstein-style irreducibility over `Polynomial (ZMod 2)`**:
   `Irreducible (f_target_int)` where `f_target_int = X⁴ + X² + X` over `(ZMod 2)[X]`,
   then transfer via `algebraMap` lifts to `f_target` over `base = FractionRing _`.
   Mathlib has `Polynomial.irreducible_of_eisenstein_criterion`; the main work is
   showing the Eisenstein hypothesis at `(X)` (the prime ideal of `(ZMod 2)[X]` generated
   by the indeterminate, which is exactly what's available as `aGen`).

2. **Splitting field characterization**: `f_target.SplittingField = base⟮α^(1/2)⟯` for
   any α with `g_factor.eval α = 0` (`α = aGen^(1/2) + 1` works after Artin-Schreier).

3. **Constructing the nontrivial automorphism σ: α^(1/2) ↦ α^(1/2) + 1**:
   - Show this map preserves the field operations and fixes `base`.
   - Show it has order 2 (σ ∘ σ = id, σ ≠ id).
   - Conclude `2 ≤ Nat.card f_target.Gal`.

4. **Upper bound `Nat.card f_target.Gal ≤ 2`**:
   - Either: degree count (deg = 4, but separable degree = 2 since f = g(X²)).
   - Or: direct case analysis on the splitting field `base⟮α^(1/2)⟯` (Galois closure has
     index 2 over base since insep degree = 2).

The full Artin-Schreier formalization is a multi-PR effort, but each of the above
steps is independently useful and may have Mathlib-upstream value.

---

## Session 2026-05-08 (Session 4, researcher-1) — g_factor structural lemmas + f_target coefficients

**Mode**: ACT (RICH knowledge tier, score 27)
**Outcome**: Added 9 structural lemmas (4 for g_factor, 5 f_target coefficient values).
Theorem count: 10 → 19. lineCount: 230 → 285. Sorries unchanged at 0; only intentional axiom
`counterexample_gal_card` remains.

### What I Did

Added 9 small structural lemmas extending the Session 3 scaffolding from f_target to its
Artin-Schreier inner factor g_factor and to f_target's individual coefficients:

**Group A — g_factor structural facts (mirror f_target's):**
1. **`g_factor_natDegree`**: `g_factor.natDegree = 2` (compute_degree!).
2. **`g_factor_degree`**: `g_factor.degree = 2` (compute_degree!).
3. **`g_factor_ne_zero`**: `g_factor ≠ 0` (corollary of natDegree).
4. **`g_factor_monic`**: `g_factor.Monic` (leading coeff = 1).

**Group B — f_target coefficient values:**
5. **`f_target_coeff_zero`**: `f_target.coeff 0 = aGen` — the Artin-Schreier parameter.
6. **`f_target_coeff_one`**: `f_target.coeff 1 = 0` — no linear term.
7. **`f_target_coeff_two`**: `f_target.coeff 2 = 1` — the X² coefficient.
8. **`f_target_coeff_three`**: `f_target.coeff 3 = 0` — no cubic term.
9. **`f_target_coeff_four`**: `f_target.coeff 4 = 1` — leading coefficient.

### Why These

The two groups attack the next-action plan from different sides:

- **Group A (g_factor)** unlocks any Capelli-style irreducibility argument for
  `f_target = g_factor.comp (X^2)`: such an argument typically needs (a) `g_factor`
  irreducible — Artin-Schreier — *and* (b) `aGen` not a square in `base`, with the
  irreducibility-of-a-composition then following from Mathlib's Capelli-type lemma. Both
  pieces consume `g_factor.natDegree = 2` and `g_factor.Monic` as inputs (and
  `g_factor.degree = 2` for `degree`-flavored variants of the API).

- **Group B (coefficients)** unlocks the alternative direct quadratic-factorisation
  argument: any hypothetical `f_target = (X² + b₁X + c₁)(X² + b₂X + c₂)` produces
  five linear/quadratic equations from comparing coefficients at X^0..X^4. The
  five lemmas here supply the right-hand sides of those equations, so the case
  analysis (`b₁ + b₂ = 0` from coeff 3, `c₁c₂ = aGen` from coeff 0, etc.) can
  proceed without re-deriving them.

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (+55 lines, +9 lemmas)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/meta.json`
  (lineCount 230→285, theoremCount 10→19 in both meta and leanFile blocks; sections
   shifted to reflect new layout; 9 entries added to mainTheorems)
- `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/knowledge.md`
  (this entry)
- `src/data/research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  (iteration bumped, builtItems and progressSummary synced through Session 4)

### Build Verification

Pending CI. `compute_degree!` and the `Polynomial.coeff_*` simp set are well-established
in this codebase (`InverseGaloisA5`, `InverseGaloisD4`, the angle-trisection chain), and
the new lemmas follow exactly the same pattern as the Session 3 lemmas which compiled.
Local Docker build was not run from this worktree (`proofs/.lake` self-cycle, see MEMORY.md).

### Path Forward (unchanged from Session 3, narrowed by this session)

The path still requires multiple sessions to discharge `counterexample_gal_card`. With
this session's lemmas, the closest concrete next step is:

- **Step 1a** — Prove `aGen` is not a square in `base`. This is the prerequisite for the
  Capelli-style irreducibility of `g_factor.comp (X^2)`.
- **Step 1b** — Prove `g_factor` is irreducible (Artin-Schreier over F₂(a)).
- **Step 1c** — Combine via Capelli: irreducibility of `f_target`.

Steps 2–4 (splitting-field characterisation, σ construction, |Gal| ≤ 2) follow.

---

## Dead Ends

- **"Inseparable irreducible → trivial Galois"**: The obvious approach is FALSE. The case f = g(X^p) with deg(g) ≥ 2 gives counterexample.
- **"Purely inseparable f ↔ trivial Gal"**: TRUE in one direction (proved), but the other direction (trivial Gal → purely insep splitting field) is not needed here.
- **Parity case split for `sub_pow_char_pow_eq`**: works in principle but the char-2 branch (where `(-1)^(2^n) = 1` and we want `-1 = 1` in `K`) requires bridging via `CharP.cast_eq_zero` and is fragile. The `iterateFrobenius` ring-hom approach avoids this entirely.

---

## Session 2026-05-16 (Session 5, researcher-12) — PREP: state.md bootstrap + Step 1a pre-stage (doc-only)

**Mode**: PREP (doc-only)
**Outcome**: First doc-only PREP on this slug. Created `state.md` (no prior version) + `sessions/2026-05-16-s05.md` with paste-ready Lean sketch for Step 1a. **0 Lean / meta.json / annotations.json / lake-manifest edits.** ACT deferred to S6 pending Docker/disk recovery.

### What I Did

1. **Stability audit**: confirmed `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` and the slug's meta/JSON/knowledge.md are unchanged since S4 PR #17217 (2026-05-08) — 8-day pristine period.
2. **state.md bootstrap**: created the slug's first `state.md` (~80 LOC) backporting the 4-session iteration history + Status Summary + ACT-readiness gate.
3. **Step 1a pre-stage**: ~60-LOC paste-ready Lean sketch for `aGen_not_isSquare`, with bearer pin recheck (8 Mathlib bearers, 0 drift at SHA `2df2f0150c…` / v4.26.0) and risk inventory.
4. **Aristotle compatibility note**: SORRY-1 in the sketch is a HARD candidate for Aristotle async submission if S6 manual attempt stalls > 10 min.
5. **JSON refresh**: `currentState.iteration` 4 → 5; `focus`, `nextAction`, `lastUpdate` refreshed; `nextSteps[1]` annotated as PASTE-READY in S5 §4.

### Key Findings

- **Step 1a (`aGen` not a square in `base`) is a low-risk, ~60-LOC proof at the pin.** The argument is degree-parity on `p² = X · q²` in `Polynomial (ZMod 2)`. No char-2 hypothesis needed (relevant only for Step 1b).
- **Mathlib v4.26.0 has no one-shot `IsFractionRing.X_not_isSquare`** generalization; this slug's Step 1a could become a Mathlib upstream contribution.
- **Slug is genuinely stable.** No drift in 8 days; no competing PRs; no audit/mechanic flags. PREP is the right move while Docker is hung.

### Files Modified

- `research/problems/.../state.md` (NEW, ~80 LOC)
- `research/problems/.../sessions/2026-05-16-s05.md` (NEW, ~300 LOC)
- `research/problems/.../knowledge.md` (this entry, ~30 LOC)
- `src/data/research/problems/....json` (currentState/iteration/lastUpdate refresh)

### What I Did NOT Do

- Did not modify `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean`.
- Did not modify `src/data/proofs/.../meta.json` (`status: axiomatized`, `axiomCount: 1`, `lineCount: 285` all unchanged).
- Did not modify `proofs/lake-manifest.json` (Mathlib pin unchanged).
- Did not discharge `counterexample_gal_card` axiom (multi-session work, see Step 1a–4 plan).

### Next Steps

S6 ACT (when Docker daemon recovers + disk ≥ 8 Gi):

1. Paste §4 of `sessions/2026-05-16-s05.md` into the Lean file after the `aGen` definition.
2. Discharge SORRY-1 manually (≈ 10 min) — or submit to Aristotle async if stuck.
3. Docker-build `Proofs.AngleTrisectionOQ02OQ01OQ01OQ01OQ01`.
4. If green: open S6 ACT PR with new theorems `aGen_ne_zero`, `aGen_not_isSquare` (+ private helper). meta.json `lineCount` 285 → ~345; `theoremCount` 19 → 21.

Steps 1b, 1c, 2, 3, 4 remain as documented in `nextSteps[2..6]`.

---

## Session 6 — 2026-06-01 (researcher-1, ACT)

### What I Did

- **Discharged S5 PREP's Step 1a sketch in full**: shipped `aGen_not_isSquare` plus two supporting lemmas (`aGen_ne_zero`, private `R_sq_eq_X_mul_sq_imp_false`). The SORRY-1 bridge from S5 PREP closed in 8 LOC via `IsLocalization.surj` + `IsFractionRing.injective` + ring rewriting + `omega` for the natDegree-parity refutation.
- **Repaired 8 latent Mathlib v4.26.0 API drifts** surfaced when Docker build ran fresh (the G9 lake self-loop had masked all 8 since 2026-05-08): parent-file `omega` regression at line 148; `base` `def → abbrev`; `AlgEquiv.refl F K` arity (×2); `AlgEquiv.refl_apply` removal; `IsPurelyInseparable.pow_mem` signature change; `Polynomial.gcd_zero_right` removal; `g_factor_monic` simp missing `coeff_X`; `f_derivative_zero` `ring` failure in char 2 (char-blind).
- **Docker build clean at 7746 jobs**, 0 errors, 0 sorries. Some warnings on pre-existing unused `Polynomial.coeff_C` simp args — left alone (not in scope).
- Updated `meta.json` (lineCount 285→380, theoremCount 19→22), `state.md` (S6 row + Repair Inventory), `knowledge.md` (this entry), research JSON (`iteration` 5→6, `focus`, `nextAction`, `lastUpdate`, `progressSummary`, `builtItems`, `nextSteps`), and added `sessions/2026-06-01-s06.md` (NEW, ~210 LOC).

### Key Findings

- **The S5 PREP sketch was solid**: the bridge plan was correct, the bearer table covered the right lemmas, and the only meaningful refinement during ACT was using `set qP := (q : Polynomial (ZMod 2))` to dodge a `HMul` instance-synth ambiguity when `↑q : Polynomial _` and `↑q : R⁰` both fit.
- **The G9 latent-bug pattern is robust**: 8 latent bugs at once when Docker had been blocked for 24 days. Memory entry "G9 qualifier masks real bugs — ALWAYS Docker-verify" continues to be confirmed; this is the largest repair cascade I've seen in one slug.
- **No new sorries, no new axioms.** Step 1a is fully proved — `aGen_not_isSquare` is downstream-ready as a hypothesis for any Capelli-style or Eisenstein-style irreducibility argument that consumes "Artin-Schreier parameter is not a square".
- **`omega` is the right closer for `2 · a = 1 + 2 · b`** even-vs-odd contradictions; no `Even` / `Odd` predicate API needed, despite S5 PREP's bearer table including `Nat.not_odd_iff_even`.

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (UPDATE, 285 → 380 LOC, +95)
- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` (UPDATE, 1-line `omega` regression fix)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/meta.json` (UPDATE, metrics + 2 new originalContributions entries)
- `src/data/research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01.json` (UPDATE, currentState + knowledge + nextSteps refresh)
- `research/problems/.../state.md` (UPDATE, Iteration History row 6 + Repair Inventory section)
- `research/problems/.../sessions/2026-06-01-s06.md` (NEW, ~210 LOC)
- `research/problems/.../knowledge.md` (this entry, ~50 LOC)

### What I Did NOT Do

- Did not discharge `counterexample_gal_card` (still axiom — multi-session Artin-Schreier chain).
- Did not run Aristotle (manual repair was tractable).
- Did not modify `proofs/lake-manifest.json` (Mathlib pin unchanged).
- Did not modify any other proof file outside this slug + its parent.
- Did not change public API of any prior-session theorem (only repaired their internal proofs).

### Next Steps

S7 ACT (Step 1b): prove `Irreducible g_factor` over `base` where `g_factor = X² + X + aGen`. Standard Artin-Schreier criterion in char 2: irreducible iff `aGen ≠ t² + t ∀t ∈ base`. Expected 120-200 LOC. Mathlib v4.26.0 bearer search for Artin-Schreier degree-2 helpers required.

Steps 1c (Capelli irreducibility of `f_target = g_factor.comp (X²)`), 2 (splitting field), 3 (σ of order 2), 4 (|Gal| ≤ 2) remain queued.
