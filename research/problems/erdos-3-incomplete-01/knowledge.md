# Knowledge: erdos-3-incomplete-01

Erdős Problem #3 ($5000, OPEN): if `∑_{a∈A} 1/a = ∞` then `A` contains
arbitrarily long arithmetic progressions.

File: `proofs/Proofs/Erdos3Problem.lean`. Two thresholds appear:
`RequiredBound k = r_k(N) = o(N/log N)` and the stronger
`StrongRequiredBound k = r_k(N) = O(N/(log N)^{1+δ})` for some `δ>0`.

---

## RESULT (2026-07-04): the strong-threshold reduction is now PROVEN (0-axiom)

A prior session designed a provable reduction at the `(log N)^{1+δ}` threshold
but could not compile it (no Mathlib build was available). This session
**compiled and verified it**, plus repaired the file, which did not build at all.

### The file did not compile on `main` (bitrot)

The enrichment adding `countingFunction_le_rothNumber` / `StrongRequiredBound`
was merged **without a build** (math PRs skip rebuild), leaving multiple hard
errors. All fixed in commit "Repair Erdos3Problem.lean bitrot":
- `ArithProg` used `Finset.map` with a bogus `by omega` injectivity proof —
  `i ↦ a + i·d` is not injective (collapses when `d = 0`), and `omega` cannot
  prove nonlinear injectivity anyway. Switched to `Finset.image` (no injectivity
  hypothesis). This is mathematically harmless: `ContainsAP` still requires
  `d > 0`, and only membership/subset facts about `ArithProg` are used.
- `rothNumber` / `countingFunction` / the bridge lemma filtered over `Set`
  membership without `Decidable` instances → added `open scoped Classical`,
  marked `countingFunction` `noncomputable`, annotated the powerset-filter
  binder as `Finset ℕ`.
- three orphaned `/-- -/` docstrings (attached to no declaration) → `/- -/`.

### The 0-axiom conditional theorem (commit "Prove strong_required_bound…")

```lean
theorem strong_required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → StrongRequiredBound k) → Erdos3Conjecture
```

Fully machine-checked, `sorry`-free, axiom-free (uses only `classical` + standard
Mathlib summability/p-series lemmas; does not touch `euler_prime_sum_diverges`).

Supporting lemmas added:
- `containsAP_of_le : k ≤ m → ContainsAP A m → ContainsAP A k` — monotonicity in
  the length (first `k` terms of an `m`-AP form a `k`-AP), via
  `Finset.image_subset_image`. Lets the main proof reduce every `k` to
  `max k 3 ≥ 3`.
- `summable_of_strongBound` — the analytic core. If
  `f_A(N) ≤ C·N/(log N)^{1+δ}` eventually (`δ>0`), then `∑_{a∈A} 1/a` converges.

**Proof of the core (dyadic blocking).** Reduce to summability of the
`ℕ`-indicator `A.indicator (1/·)` via `summable_subtype_iff_indicator`, then to
bounded partial sums via `summable_of_sum_range_le`. For each `M`,
`∑_{i<M} ≤ ∑_{i<2^M}`, which regroups (induction, `sum_Ico_consecutive`) into
dyadic blocks `∑_{j<M} block_j`, `block_j = ∑_{i∈[2^j,2^{j+1})} A.indicator(1/·) i`.
Two bounds on each block:
- crude: `block_j ≤ 1` (`|[2^j,2^{j+1})| = 2^j` terms, each `≤ 1/2^j`);
- strong (`j ≥ N0`): `block_j ≤ |A∩[2^j,2^{j+1})|/2^j ≤ f_A(2^{j+1})/2^j
  ≤ 2C/((j+1)·log 2)^{1+δ} =: g j`, using `Real.log (2^{j+1}) = (j+1)·log 2`
  and `Real.mul_rpow`.
Hence `block_j ≤ 𝟙[j<N0] + g j`, so `∑_{j<M} block_j ≤ N0 + ∑' g`, and `g`
is a constant multiple of the convergent p-series `∑ 1/(j+1)^{1+δ}`
(`Real.summable_one_div_nat_rpow`, `p = 1+δ > 1`, reindexed by
`summable_nat_add_iff`). Bounded partial sums ⟹ summable ⟹ contradiction with
`HasDivergentSum`.

The main theorem combines this with the bridge lemma
`countingFunction_le_rothNumber` (AP-free ⟹ `f_A(N) ≤ r_k(N)`).

---

## Why the WEAKER `o(N/log N)` threshold is still an honest sorry

`required_bound_implies_conjecture` (hypothesis `RequiredBound = o(N/log N)`)
remains `sorry`. This is **not** laziness: at that threshold the implication is
as hard as Erdős #3 itself. `f_A(N) = o(N/log N)` does not force `∑1/a < ∞`:
the borderline profile `f(N) ≍ N/(log N·log log N)` is `o(N/log N)` yet has
divergent reciprocal sum (`∑ f(n)/n² ≍ ∫ dt/(t·log t·log log t) = log log log t
→ ∞`). Whether such a set can also be AP-free is exactly the open content of
Erdős #3. The gap between `o(N/log N)` and `O(N/(log N)^{1+δ})` is precisely
where the difficulty lives — which is what the new theorem makes explicit.

Best known Roth-type bounds (Kelley–Meka 2023 `r_3(N) ≪ N/exp((log N)^{1/11})`,
Leng–Sah–Sawhney 2024) are far from even `o(N/log N)`, let alone the
`(log N)^{1+δ}` threshold.

---

## File inventory (`Proofs/Erdos3Problem.lean`, 440 lines, builds: 7743 jobs)

- Defs: `ArithProg` (now `image`), `ContainsAP`, `ContainsArbitrarilyLongAP`,
  `IsAPFree`, `reciprocalSum`, `HasDivergentSum`, `rothNumber`,
  `countingFunction`, `SublogarithmicGrowth`, `Erdos3Conjecture`,
  `RequiredBound`, `StrongRequiredBound`.
- Proved (0 new axioms): `countingFunction_le_rothNumber`, `containsAP_of_le`,
  `summable_of_strongBound`, `strong_required_bound_implies_conjecture`,
  `erdos3_implies_green_tao`, `erdos_3_open`.
- 1 axiom: `euler_prime_sum_diverges` (Euler 1737; deep, kept).
- 1 sorry: `required_bound_implies_conjecture` (threshold-critical; open).

## Status

PROGRESS. Delivered this session: (1) repaired a non-compiling file (bitrot);
(2) proved, 0-axiom and sorry-free, `strong_required_bound_implies_conjecture`,
the reduction at the correct `(log N)^{1+δ}` threshold, machine-verified in
Lean 4 / Mathlib 4.26. The original `o(N/log N)` sorry is correctly retained as
threshold-critical (as hard as Erdős #3).

## Update (2026-07-04, attempt 3): unconditional base cases k ≤ 2 PROVEN

Followed the first shallow follow-up below. Added, machine-checked (7743 jobs),
0-axiom and sorry-free:
- `infinite_of_hasDivergentSum : HasDivergentSum A → A.Infinite`. Proof: finite
  `A` is a `Fintype`, over which `hasSum_fintype` gives summability, contradicting
  divergence. This is the hypothesis-side twin of the existing conclusion-side
  `infinite_of_containsArbitrarilyLongAP` — both sides of Erdős #3 only bite on
  infinite sets.
- `containsAP_two_of_lt {a b} (ha : a∈A) (hb : b∈A) (hab : a<b) : ContainsAP A 2`,
  witness `(a, b-a)`: `ArithProg a (b-a) 2 = {a, b} ⊆ A`.
- `containsAP_two_of_infinite : A.Infinite → ContainsAP A 2` via
  `Set.Infinite.nontrivial`.
- `erdos3_holds_length_le_two : HasDivergentSum A → k ≤ 2 → ContainsAP A k`,
  combining the above with `containsAP_of_le` length-monotonicity. The honest
  **unconditional** slice of Erdős #3 (no Roth threshold needed): the difficulty
  is entirely in k ≥ 3.

Gotcha noted for reuse: in `containsAP_two_of_lt`, the `i = 1` `interval_cases`
branch has goal `a + 1*(b-a) ∈ A`; `simpa [h]` fails because `one_mul` fires
before the rewrite `h : a + 1*(b-a) = b` can match. Use `show a + 1*(b-a) ∈ A;
rw [h]; exact hb` to pin the pre-simp form.

Gallery `meta.json` synced (lineCount 163/486→614, theoremCount 3/10→16).

## Update (2026-07-04, attempt 4): two reusable structural lemmas PROVEN

Followed the last two shallow follow-ups. Added, machine-checked (7743 jobs),
0-axiom and sorry-free:
- `rothNumber_mono_length {k m N} (hkm : k ≤ m) : rothNumber k N ≤ rothNumber m N`.
  `r_k(N)` is monotone in the progression length. Proof: `IsAPFree A k →
  IsAPFree A m` for `m ≥ k` (an `m`-AP contains a `k`-AP via `containsAP_of_le`,
  contrapositive), so the `k`-AP-free subfamily of `(range (N+1)).powerset` is a
  subset of the `m`-AP-free one; `Finset.sup_mono` lifts the subset to the sup.
  Density-side twin of `containsAP_of_le` (length-monotonicity of `ContainsAP`),
  completing the "longer APs are easier to avoid" picture.
- `not_hasDivergentSum_of_strongBound (hδ hC hbound) : ¬ HasDivergentSum A`.
  Contrapositive packaging of `summable_of_strongBound`, exposing it as a
  standalone density ⇒ convergence criterion: `f_A(N) ≤ C·N/(log N)^{1+δ}`
  eventually (`δ>0`) forbids a divergent reciprocal sum. Reusable for any other
  reciprocal-sum problem sitting at the `(log N)^{1+δ}` threshold.

Gallery `meta.json` synced (lineCount 614 → 646, theoremCount 16 → 18).

## Next steps

- The remaining `sorry` should NOT be attacked directly — it is as hard as
  Erdős #3. Leave it documented.
- The `k ≤ 2` corollary, the length-monotonicity of `r_k`, and the reusable
  density⇒convergence criterion are now all DONE. The shallow-follow-up surface
  is essentially exhausted; further honest progress needs the deep analytic
  content of Erdős #3 itself.
