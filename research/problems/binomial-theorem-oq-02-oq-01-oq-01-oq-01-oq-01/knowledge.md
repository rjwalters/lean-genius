# Knowledge — binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01

S1 OBSERVE audit (2026-05-12, researcher-10).

## 1. The Multinomial Theorem in Mathlib v4.26.0 (pin `2df2f015`)

The multinomial theorem for any `CommSemiring R` lives at
`Mathlib/Data/Nat/Choose/Multinomial.lean`, namespace `Finset`,
line 301-304 in the pinned revision:

```lean
section CommSemiring
variable [CommSemiring R] {f : α → R} {s : Finset α}

lemma sum_pow_eq_sum_piAntidiag (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n =
      ∑ k ∈ piAntidiag s n, multinomial s k * ∏ i ∈ s, f i ^ k i := by
  simp_rw [← noncommProd_eq_prod]
  rw [← sum_pow_eq_sum_piAntidiag_of_commute _ _ fun _ _ _ _ _ ↦ Commute.all ..]
```

(Verified at `gh api repos/leanprover-community/mathlib4/contents/
Mathlib/Data/Nat/Choose/Multinomial.lean?ref=2df2f015...`, file
length 358 lines, lemma at 301-304.)

The `noncommutative` variant (`sum_pow_eq_sum_piAntidiag_of_commute`,
line 220) is the same statement under the weaker
`Pairwise (Commute on f)` hypothesis, proved by induction on `s`
via `Finset.cons_induction`. Our target instantiation has
`R := ENNReal` (commutative), so the commutative form is the right
hook.

### Multinomial coefficient type

In the same file, `Nat.multinomial : Finset α → (α → ℕ) → ℕ` is
defined at line 43:

```lean
def multinomial (s : Finset α) (f : α → ℕ) : ℕ :=
  (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!
```

with `multinomial_pos`, `multinomial_spec`, and a battery of
specialization lemmas (`multinomial_empty`,
`multinomial_singleton`, `binomial_eq_choose`,
`multinomial_univ_two`, `multinomial_univ_three`).

### piAntidiag

`Finset.piAntidiag` is defined in `Mathlib/Combinatorics/Enumerative/
DoubleCounting/PiAntidiag.lean` (or `Mathlib/Data/Finset/Antidiagonal.lean`,
location stable across recent revs). Its membership characterization:

```lean
f ∈ s.piAntidiag n ↔ (∑ i ∈ s, f i = n) ∧ (∀ i, f i ≠ 0 → i ∈ s)
```

This precisely matches the data in the `Composition` structure used
by the gallery (sum-equals-n plus support-in-s).

## 2. The Parent Gallery File

`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean` (265 lines, 5 sorries,
0 axioms, `namespace BinomialTheoremOQ02OQ01OQ01`) defines:

* `Composition α s n` (lines 41-47): the same structure as in
  `BinomialTheoremOQ02OQ01OQ01OQ01.lean` (sibling), with fields
  `counts`, `sum_eq`, `counts_outside`. NOTE: the two structures
  are in different namespaces but otherwise identical; the
  type-equivalence is trivial.
* `instance : Fintype (Composition α s n)` (lines 58-69), proved via
  `Fintype.ofEquiv` with the `piAntidiag` bridge inlined.
* `multinomialPMFVal s p n k : ℝ≥0∞` (lines 80-83):
  `multinomial s k.counts * ∏ i ∈ s, p i ^ k.counts i`.
* `theorem multinomialPMF_sum_eq_one ... := by sorry` (lines 98-102).
  **THIS IS THE TARGET.**
* `noncomputable def multinomialPMF s p n hp : PMF (Composition α s n)`
  (lines 112-116): trivially uses `multinomialPMF_sum_eq_one` as the
  `PMF.tsum_coe = 1` witness.
* Four more sorries downstream (`multinomialPMF_support`,
  `multinomial_marginal_binomial`, `multinomial_mean`,
  `multinomial_covariance`); all OUT OF SCOPE for this slug.

## 3. The Sibling Child File (Source of the Bridge)

`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01.lean` (186 lines,
0 sorries, 0 axioms, `namespace CompositionFintype`) provides:

* `Composition α s n` — same shape, different namespace.
* `compositionEquiv : Composition α s n ≃ ↥(s.piAntidiag n)` —
  ~20 line proven equivalence.
* `instFintypeComposition` — Fintype via `Fintype.ofEquiv`.
* `card_composition`, `card_composition_zero` — cardinality lemmas.
* `dice_six_rolls_all_different` — concrete `native_decide` exhibit.
* `sum_composition_eq_piAntidiag_sum {α} [DecidableEq α] {M}
  [AddCommMonoid M] (s : Finset α) (n : ℕ) (f : (α → ℕ) → M) :
  ∑ c : Composition α s n, f c.counts = ∑ k ∈ s.piAntidiag n, f k`
  (lines 145-153, ~8 line proof).
  **THIS IS THE STRUCTURAL BRIDGE.**

Proof of the bridge:

```lean
theorem sum_composition_eq_piAntidiag_sum ... := by
  rw [← Finset.sum_coe_sort (s.piAntidiag n)]
  exact Fintype.sum_equiv (compositionEquiv α s n) _ _ (fun c => rfl)
```

## 4. The Namespace Bridge Sub-Problem

The two `Composition` types in §2 and §3 are structurally
identical but Lean treats them as distinct. The S2 ACT file must
either:

* **(Option A) Bridge equivalence.** Define
  ```lean
  def compositionTypeEquiv (α : Type*) [DecidableEq α]
      (s : Finset α) (n : ℕ) :
      BinomialTheoremOQ02OQ01OQ01.Composition α s n ≃
      CompositionFintype.Composition α s n :=
    { toFun := fun c => ⟨c.counts, c.sum_eq, c.counts_outside⟩
      invFun := fun c => ⟨c.counts, c.sum_eq, c.counts_outside⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => by cases c; rfl }
  ```
  Then use `Fintype.sum_equiv compositionTypeEquiv` to lift sums
  between the two presentations.

* **(Option B) Direct mirror.** Re-prove
  `sum_composition_eq_piAntidiag_sum` inside the
  `BinomialTheoremOQ02OQ01OQ01` namespace by inlining the
  `compositionEquiv` construction at the local `Composition`. This
  duplicates ~20 lines from the sibling file.

Option A is preferred because (i) it makes the bridge explicit and
discoverable for future similar slugs and (ii) it does not duplicate
the equivalence work. The PR description should call out the design
choice.

Estimated S2 ACT file size: ~50-60 lines for option A, ~70-80 for
option B.

## 5. ENNReal as a `CommSemiring`

`ENNReal` (alias `ℝ≥0∞ := WithTop ℝ≥0`) carries a `CommSemiring`
instance via `Mathlib.Topology.Instances.ENNReal`. Key facts for the
proof:

* `one_pow n : (1 : ENNReal) ^ n = 1` — folds `1^n` after applying
  `hp` to rewrite `∑ p i = 1`.
* `ENNReal.one_pow` (specialized form, available in the same file).
* The multinomial theorem applies because `ENNReal` is a
  `CommSemiring` (in fact a `OrderedCommSemiring` and more).

No infinity-arithmetic concern arises because `1` is finite; the
proof never sees `⊤`.

## 6. Risks (Lean-side)

* **Decidable equality.** The Mathlib lemma assumes `[DecidableEq α]`
  on the index. The parent file already requires this on every
  multinomial theorem (line 41 onward). No new typeclass hypothesis.

* **Function-level equality.** After applying
  `sum_composition_eq_piAntidiag_sum`, the summand becomes a function
  of `k : α → ℕ` rather than `k : Composition`. The shape after the
  rewrite is:
  ```
  ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : ℝ≥0∞) * ∏ i ∈ s, p i ^ k i
  ```
  which exactly matches the RHS of `Finset.sum_pow_eq_sum_piAntidiag`
  with `f := p` (modulo coercion of the natural-number multinomial
  to `ℝ≥0∞`, which is automatic via `Nat.cast`).

* **No `simp` loop risk.** The proof is a linear sequence
  (`rw [sum_composition_eq_piAntidiag_sum]`,
  `rw [← Finset.sum_pow_eq_sum_piAntidiag]`,
  `rw [hp]`, `rw [one_pow]`), no recursion.

* **Mathlib drift.** `Finset.sum_pow_eq_sum_piAntidiag` has been
  stable since Mathlib v4.10+ (no name changes through v4.26.0
  per the manifest). Low drift risk.

## 7. Open API Questions (to resolve in S2 ACT-A)

* **Q1.** Should the new file `BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean`
  re-export the `BinomialTheoremOQ02OQ01OQ01.multinomialPMFVal` /
  `multinomialPMF` names with the proved normalization, or live as a
  pure proof-of-existence file? — **Recommendation**: pure
  proof-of-existence (state the theorem; do not redefine the PMF).
  The downstream consumers should import this file and apply the
  proven theorem via the existing `multinomialPMF` definition.

* **Q2.** Should the file be added to `proofs/Proofs.lean` so that the
  whole-tree build picks it up? — **Yes**, alphabetical position
  between `BinomialTheoremOQ02OQ01OQ01OQ01.lean` and
  `BinomialTheoremOQ02OQ01OQ01OQ02.lean`. Verify this position
  before push.

* **Q3.** Does the proof need a `coe`/`push_cast` step for
  `(Nat.multinomial : ℕ) → (ℝ≥0∞)`? — `Nat.cast` is automatic but
  the rewrite may need `simp only [Nat.cast_ofNat]` or
  `push_cast` to fully match. Expect ~2 lines of `simp` after the
  main `rw`s.

## 8. Candidate Proof Skeleton (S2 ACT-A)

```lean
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ01
import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01

namespace BinomialTheoremOQ02OQ01OQ01

open Finset BigOperators ENNReal

/-- Namespace bridge: the local and sibling `Composition` types
    are structurally identical, hence equivalent. -/
def compositionTypeEquiv (α : Type*) [DecidableEq α]
    (s : Finset α) (n : ℕ) :
    Composition α s n ≃ CompositionFintype.Composition α s n where
  toFun  c := ⟨c.counts, c.sum_eq, c.counts_outside⟩
  invFun c := ⟨c.counts, c.sum_eq, c.counts_outside⟩
  left_inv  := fun c => by cases c; rfl
  right_inv := fun c => by cases c; rfl

/-- **Normalization of the multinomial PMF** (proven).
    Combines `sum_composition_eq_piAntidiag_sum` with Mathlib's
    `sum_pow_eq_sum_piAntidiag`. -/
theorem multinomialPMF_sum_eq_one_proved
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ENNReal) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) :
    ∑ k : Composition α s n, multinomialPMFVal s p n k = 1 := by
  -- 1. Transfer the sum to CompositionFintype.Composition.
  rw [Fintype.sum_equiv (compositionTypeEquiv α s n)
      (fun k => multinomialPMFVal s p n k)
      (fun k => (Nat.multinomial s k.counts : ℝ≥0∞) * ∏ i ∈ s, p i ^ k.counts i)
      (fun _ => rfl)]
  -- 2. Transfer the CompositionFintype sum to piAntidiag.
  rw [CompositionFintype.sum_composition_eq_piAntidiag_sum]
  -- 3. Apply Mathlib's multinomial theorem in reverse.
  rw [← Finset.sum_pow_eq_sum_piAntidiag s p n]
  -- 4. Apply hp and 1^n = 1.
  rw [hp, one_pow]

end BinomialTheoremOQ02OQ01OQ01
```

Caveats: the `Fintype.sum_equiv` arrow direction and the unfolding
of `multinomialPMFVal` may need a 1-line `simp only
[multinomialPMFVal]` or `show` insertion to make the
`Fintype.sum_equiv` motive elaborate. These are mechanical S2 ACT-A
moves, not S1 OBSERVE concerns.

## 9. Estimated S2 ACT-A Effort

* Code: 40-60 lines of Lean.
* Time: 30-60 minutes to write, 20-30 minutes to Docker-build (with
  fresh Mathlib clone if `.lake` symlink is broken per project
  memory).
* Risk of build-pending: moderate; the file is short and depends only
  on stable Mathlib API. If the Docker container times out, file as
  "build pending" per project convention.

## 10. Out of Scope for This Slug

* Discharging the other four sorries in
  `BinomialTheoremOQ02OQ01OQ01.lean`.
* Upstreaming a Mathlib `PMF.multinomial` constructor.
* Generalizing beyond `ENNReal` (the `PMF` type fixes the codomain).
* Refactoring to merge the two `Composition` namespaces into one
  canonical definition.
