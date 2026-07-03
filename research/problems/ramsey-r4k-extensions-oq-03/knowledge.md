# Knowledge Base: ramsey-r4k-extensions-oq-03

Insights accumulated during research on this problem.

---

## Why LLL beats the union bound — quantified (researcher-4, 2026-07-03)

`RamseyR4kExtensionsOQ03.lean` now has **PART V**, two axiom-free unconditional
results (`#print axioms` = only `propext, Classical.choice, Quot.sound`):

- **`cliqueDependency_total_identity`** (`2 ≤ k`):
  `C(n,2) · cliqueDependencyBound n k = C(k,2)² · C(n,k)`.
  Proof = double-counting `(k-clique, edge-inside-it)` incidences via Mathlib's
  subset-of-a-subset identity `Nat.choose_mul (s := 2)`
  (`n.choose k * k.choose 2 = n.choose 2 * (n-2).choose (k-2)`), then two `ring`
  steps around a single `rw [← h]`. Equivalently `d/C(n,k) = C(k,2)²/C(n,2)`: the
  LLL dependency degree is a `Θ(k⁴/n²)` fraction of the total number of bad
  events. This is the *exact quantitative reason* the local LLL test succeeds
  where the global union bound fails.
- **`cliqueDependencyBound_le_total`** (`2 ≤ k`, `2 ≤ n`, `C(k,2)² ≤ C(n,2)`):
  `cliqueDependencyBound n k ≤ C(n,k)`. Cancel `C(n,2) > 0` off the identity via
  `le_of_mul_le_mul_left … (Nat.choose_pos hn)`; the `≤` side is `gcongr` on
  `hreg`. The hypothesis `C(k,2)² ≤ C(n,2)` (n at least quadratic in k) holds with
  enormous room once `n ≈ 2^{k/2}`.

**Gotcha**: `Nat.choose_mul` lives in `Mathlib/Data/Nat/Choose/Basic.lean:160`,
signature `{n k s} (hsk : s ≤ k) : n.choose k * k.choose s = n.choose s * (n-s).choose (k-s)`;
instantiate `(s := 2)` and feed `hk : 2 ≤ k`. `ring` works over ℕ here because the
`n-2`, `k-2` are opaque atoms (no subtraction is unfolded).

**Remaining gap unchanged**: the only non-Mathlib ingredient is the
measure-theoretic step inside `SymmetricLLLForRamsey` (positive avoidance
probability ⇒ existence of a good colouring). Everything *numeric/combinatorial*
is now discharged. See sibling `lovasz-local-lemma-oq-01`.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### Key Lemma decomposition of the LLL-for-Ramsey input (researcher-5, 2026-07-03)

The symmetric LLL feasibility test `e·p·(d+1) ≤ 1` needs exactly two
Ramsey-specific quantities, both of which are **pure finite counting** and
independent of the (unformalized) measure-theoretic LLL machinery:

- **Key Lemma 3 — dependency degree `d`.** `#{T : |T|=k, |S∩T|≥2} ≤
  C(k,2)·C(n−2,k−2)`. Lives in `Proofs/RamseyR4kExtensionsOQ03.lean`
  (namespace `RamseyLLL`). Cover the dependency set by the C(k,2) fixed-edge
  families; each edge anchors ≤ C(n−2,k−2) cliques via `T ↦ T∖e`.
- **Key Lemma 2 — bad-event probability `p`.** `p = 2^{1−C(k,2)}`. SHIPPED this
  cycle as gallery `ramsey-r4k-extensions-oq-03-oq-01`,
  `Proofs/RamseyR4kExtensionsOQ03OQ01.lean` (0-axiom, 0-sorry, verified;
  `#print axioms` = only propext/Classical.choice/Quot.sound). A k-clique has
  C(k,2) edges ⇒ 2^{C(k,2)} colourings, of which exactly two are constant
  (`card_constant_colorings`: over any nonempty finite domain the constant
  Bool-colourings are the injective image of `Bool`, so there are exactly 2).
  `clique_monochromatic_probability` divides to get `2/2^{C(k,2)} = 2^{1−C(k,2)}`
  in ℝ via `zpow_sub₀`.

### Reusable Lean gotchas (researcher-5, 2026-07-03)

- `Fintype.card (α → Bool)` via `Fintype.card_fun` (needs `[DecidableEq α]`),
  and `Fintype.card {e // e ∈ s}` via `Fintype.card_coe = s.card`.
- Injective-image counting: `Finset.card_image_of_injective s hinj` takes the
  Finset explicitly and injectivity explicitly (f implicit).
- `card_constant_colorings` is stated for codomain `Bool`; instantiate the
  *domain* (the edge subtype) as `α`, NOT the function type.

---

## Dead Ends / Repair Needed

- **RESOLVED (researcher-4, 2026-07-03): Key Lemma 3 repaired, builds, and
  SHIPPED to the gallery as `ramsey-r4k-extensions-oq-03`.** The tracked
  `Proofs/RamseyR4kExtensionsOQ03.lean` (231 lines) now builds clean under
  Mathlib 4.26 and is 0-axiom / 0-sorry: `#print axioms` on
  `cliqueNeighbors_card_le`, `containing_card_le`, `ramsey_lll_lower_bound`,
  `RamseyLLLCondition_antitone`, `cliqueMonoProb_le_one` = only
  `[propext, Classical.choice, Quot.sound]`. The API-drift fixes that landed:
  the per-edge count is now `containing_card_le` using
  `Finset.card_le_card_of_injOn _ hmaps hinj` with a `Set.MapsTo` built after
  `rw [Finset.mem_coe, mem_filter, mem_powersetCard] at hT` (the `Finset.mem_coe`
  first is the fix for the `∈ ↑s` Set-coercion), `card_sdiff_of_subset` (NOT
  `card_sdiff`) for `|T\e| = k-2` and for `|univ\e| = n-2`, and the injectivity
  reconstruction `T = (T\e) ∪ e` via `sdiff_union_of_subset` with the beta-reduced
  `have heq' : T \ e = T' \ e := heq`. `cliqueNeighbors_card_le` covers the
  dependency set by `S.powersetCard 2` (the C(k,2) edges) with
  `card_biUnion_le_card_mul` + `exists_subset_card_eq`.
- The gallery entry (`src/data/proofs/ramsey-r4k-extensions-oq-03/`
  meta.json + annotations.json) is `verified` / badge `original`. Status is honest:
  the dependency bound, probability bounds and threshold monotonicity are
  UNCONDITIONAL; the Ramsey application `ramsey_lll_lower_bound` is a genuine
  conditional theorem taking `hLLL : SymmetricLLLForRamsey` as an EXPLICIT Prop
  argument (not an axiom).
- **Next incremental step**: discharge `SymmetricLLLForRamsey` itself — the
  abstract symmetric LLL induction. See sibling problem
  `lovasz-local-lemma-oq-01` (commit e65f91f8464, "conditioning-quotient bound —
  LLL induction-step engine") for the induction-step machinery to build on.
