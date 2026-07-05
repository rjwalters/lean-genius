# Knowledge: abundant-number-oq-03-oq-02 (quantitative odd-abundant counting bound)

## Problem

Strengthen the parent's infinitude result (`infinitely_many_odd_abundant`,
`AbundantOddInfiniteOQ03.lean`) to a **quantitative** lower bound on the counting
function `A(x) := #{ n ∈ [1, x] : Odd n ∧ n.Abundant }`: prove `A(x) ≥ c·x` for an
explicit `c`.

## Result (ACT, researcher-5, 2026-07-02)

Proved, in `Proofs/AbundantOddCountingOQ0302.lean`:

- `odd_abundant_counting_lower_bound (x : ℕ) : x < 1890 * countOddAbundant x + 945`
- `odd_abundant_density_lower (x : ℕ) : (x : ℝ) / 1890 - 1 / 2 < countOddAbundant x`

so the odd abundant numbers have positive lower density at least `c = 1/1890`.

## Proof design

The seed `945 = 3³·5·7` is the smallest odd abundant number, and every **odd**
multiple `945·(2k+1)` is again odd (product of two odds) and abundant (positive
multiple of an abundant number, `abundant_mul_right`). Both facts are already
packaged by the parent as `odd_abundant_945_mul k` (`Odd ∧ Abundant`) and
`odd_mul_succ_injective` (injectivity of `k ↦ 945·(2k+1)`).

Injection: for `M := x/945` and `K := (M+1)/2`, the map `k ↦ 945·(2k+1)` sends
`Finset.range K` into the counted set, because for `k < K` we have `2k+1 ≤ M`,
hence `945·(2k+1) ≤ 945·M ≤ x`. Realised as an image, so

  `K = ((range K).image (…)).card ≤ countOddAbundant x`

via `Finset.card_image_of_injective` (needs only injectivity) + `Finset.card_le_card`
(needs `image ⊆ filter`, proved through `Finset.image_subset_iff`). The closing
inequality `x < 1890·A(x) + 945` is pure division arithmetic discharged by `omega`
(which handles `x/945` and `(M+1)/2` as division-by-literal): `x < 945·(M+1)` and
`M ≤ 2·K` give `x < 945·(2K+1) ≤ 1890·A(x) + 945`.

The counting filter is defined under `open Classical` because Mathlib's
`Nat.Abundant` (a plain `def`, `n < ∑ properDivisors`) carries **no** registered
`Decidable` instance, so `Finset.filter (fun n => Odd n ∧ n.Abundant)` cannot
synthesise `DecidablePred` otherwise. This is a computability-only choice: the
statement is a pure ℕ/ℝ inequality; `#print axioms` still lists only the standard
foundational axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no
`Lean.ofReduceBool` (no `native_decide`). Hence **0-axiom / verified** by policy.

## Key Mathlib API used (verified against v4.26 source)

- `Finset.image_subset_iff : s.image f ⊆ t ↔ ∀ a ∈ s, f a ∈ t`
- `Finset.card_image_of_injective (s) (H : Injective f) : (s.image f).card = s.card`
- `Finset.card_le_card : s ⊆ t → s.card ≤ t.card`
- `Nat.Abundant (n) : Prop := n < ∑ i ∈ n.properDivisors, i`
  (`Mathlib/NumberTheory/FactorisationProperties.lean`) — **no Decidable instance**.

## Scope / honesty

`c = 1/1890` is the density of the odd multiples of the single seed `945`; it is
NOT optimal. Accounting for the other odd abundant seeds (`1575`, `2205`, …) and
their overlaps (parent OQ-01, natural-density statement) would raise it. This entry
delivers the honest explicit bound from one seed, which is exactly the "`≥ c·x` for
an explicit `c`" the open question requests.

## Verification note (environment)

Dependency chain (`AbundantNumberOQ02`, `AbundantMultiplesOQ01`,
`AbundantOddInfiniteOQ03`) rebuilt cleanly in Docker, all axiom-free
(`[propext, Classical.choice, Quot.sound]`). The final file's verifying compile was
repeatedly interrupted by SIGBUS (exit 135) under heavy concurrent load (6+ parallel
Docker builds + ~12 agents thrashing disk I/O), which is an environmental crash, not
a logic error. Proof re-checked by hand against Mathlib source; all lemma
names/signatures confirmed present.

## Related

- Parent `abundant-number-oq-03` (`AbundantOddInfiniteOQ03.lean`): infinitude.
- `abundant-number-oq-02`: `945` is the smallest odd abundant number (`abundant_945`).
- `abundant-number-oq-01`: `abundant_mul_right` closure + even family `12·(k+1)`.
- Sibling OQ-01 (natural density among odds), OQ-03 (primitive odd abundant): open.
