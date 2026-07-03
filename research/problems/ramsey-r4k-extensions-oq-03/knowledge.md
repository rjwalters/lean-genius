# Knowledge Base: ramsey-r4k-extensions-oq-03

Insights accumulated during research on this problem.

---

## PART VII — honest comparison with the OPTIMIZED union bound (researcher-4, 2026-07-03)

**Mode**: REVISIT (RICH, score 20). **Outcome**: progress (4 new axiom-free theorems, still 0 sorries/0 axioms, builds Mathlib 4.26).

### Motivation / correction
The entry advertised the LLL as "beating the first moment" via `R(6,6)>13` vs
`R(6,6)>8`. But `8 = 2^{⌊6/2⌋}` is the **weakened closed-form** first moment, not
the sharp optimum. The honest optimized union bound `E[# mono k-cliques] < 1 ⟺
2·C(n,k) < 2^{C(k,2)}` reaches `R(6,6) > 17` and `R(7,7) > 27`, **strictly beating**
the LLL region (13, 22). So the symmetric-LLL setup of this file does **not** improve
on the sharp union bound at small `k`; its factor-`Θ(k)` gain is genuinely asymptotic.

### Added (PART VII in `RamseyR4kExtensionsOQ03.lean`)
- **`firstMomentCondition n k`** `:= 2·C(n,k) < 2^{C(k,2)}` — the sharp union-bound
  test; `Decidable` by `infer_instance` after `unfold`.
- **`lll_core_eq_firstMoment_core`** (`2 ≤ k`): `C(n,2)·(6·d) = 3·C(k,2)²·(2·C(n,k))`.
  Rescale `cliqueDependency_total_identity` by 6 (needs `(n := n) (k := k)` to pin the
  implicit `n` in the standalone `have`, else "don't know how to synthesize `n`").
  Both tests compare their core to the same budget `2^{C(k,2)}`, so the ratio
  `3·C(k,2)²/C(n,2)` is the **exact finite crossover criterion**.
- **`lll_core_le_firstMoment_core`** (`2 ≤ k`, `2 ≤ n`, `3·C(k,2)² ≤ C(n,2)`):
  `6·d ≤ 2·C(n,k)` (LLL more permissive in the large-`n`, `n≳k²` regime).
  `rw [core_eq]; gcongr` then cancel `C(n,2)>0`.
- **`unionBound_beats_lll_at_6` / `_at_7`**: `firstMomentCondition 17 6 ∧
  ¬RamseyLLLCondition 17 6` and same at `(27,7)`; `refine ⟨by decide, ?_⟩;
  rw [ramseyLLLCondition_iff]; decide`.

Numeric check (crossover): `3·C(6,2)² = 675 > 136 = C(17,2)` → small-`n` side, union
bound wins at `k=6`, consistent with the theorems. LLL only overtakes once
`3·C(k,2)² < C(n,2)`, i.e. `n` at least ~quadratic in `k` (the `n≈2^{k/2}` regime).

### Still open (unchanged)
The sole remaining piece is the symmetric-LLL avoidance principle
`SymmetricLLLForRamsey` (Spencer's conditional-probability induction); not in Mathlib.

---

## PART VI — why LLL beats the union bound, quantified (researcher-4, 2026-07-03)

Appended to `RamseyR4kExtensionsOQ03.lean` on top of the decidable-criterion
PART V (integer test `6·(d+1) ≤ 2^{C(k,2)}` + concrete `R(6,6)>13`, `R(5,5)>7`
witnesses). Two axiom-free unconditional theorems (`#print axioms` = only
`propext, Classical.choice, Quot.sound`):

- **`cliqueDependency_total_identity`** (`2 ≤ k`):
  `C(n,2) · cliqueDependencyBound n k = C(k,2)² · C(n,k)`. Double-count
  `(k-clique, edge-inside-it)` incidences via Mathlib's subset-of-a-subset
  identity `Nat.choose_mul (s := 2)`
  (`n.choose k * k.choose 2 = n.choose 2 * (n-2).choose (k-2)`), then two `ring`
  steps around one `rw [← h]`. Gives `d/C(n,k) = C(k,2)²/C(n,2)`: the LLL
  dependency degree is a `Θ(k⁴/n²)` fraction of the total bad-event count — the
  exact reason the *local* LLL test succeeds where the *global* union bound fails.
- **`cliqueDependencyBound_le_total`** (`2 ≤ k`, `2 ≤ n`, `C(k,2)² ≤ C(n,2)`):
  `d ≤ C(n,k)`. Cancel `C(n,2) > 0` via
  `le_of_mul_le_mul_left … (Nat.choose_pos hn)`; `≤` side by `gcongr`.

**Gotcha**: `Nat.choose_mul` is in `Mathlib/Data/Nat/Choose/Basic.lean:160`,
`{n k s} (hsk : s ≤ k) : n.choose k * k.choose s = n.choose s * (n-s).choose (k-s)`;
instantiate `(s := 2)`, feed `hk : 2 ≤ k`. `ring` works over ℕ since `n-2`, `k-2`
stay opaque atoms.

**Remaining gap unchanged**: the only non-Mathlib ingredient is the
measure-theoretic step inside `SymmetricLLLForRamsey` (positive avoidance
probability ⇒ existence). All numeric/combinatorial content is now discharged.
See sibling `lovasz-local-lemma-oq-01`.

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

- **`Proofs/RamseyR4kExtensionsOQ03.lean` (Key Lemma 3) does NOT build under
  Mathlib 4.26 as of 2026-07-03** — it was left as untracked WIP by an earlier
  researcher and never merged. Multiple API-drift failures in
  `edge_containing_cliques_card_le`: `Finset.card_le_card_of_injOn` now hands the
  "maps into" hypothesis with `∈ ↑s` (Set coercion), so `rw [Finset.mem_filter,
  Finset.mem_powersetCard] at hT` fails (pattern `_ ∈ filter _ _` not found — need
  `Finset.mem_coe` first); `Finset.card_sdiff (Finset.subset_univ e)` reports
  "function expected"; and the final injectivity step needs `heq` beta-reduced
  (`have hsdiff : T1 \ e = T2 \ e := heq` works, plain `rw [heq]` does not).
  Key Lemma 2 was shipped standalone precisely because it is self-contained and
  verified; repairing Key Lemma 3 is the next incremental step.
