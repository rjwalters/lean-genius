# Knowledge Base: erdos-476-oq-05-wip-01

**Last Updated**: 2026-04-26
Insights accumulated during research on this problem.

---

## Session 2026-04-26 (Session 3) — B-All-Redundancy Analysis; |A|≥4,|B|≥3 Sorry Confirmed Blocked

**Mode**: REVISIT
**Outcome**: blocked (deeper analysis; no Lean code changes)

### What I Did

- Analyzed the remaining sorry at line 844 (`|A|≥4 or |B|≥4` all-redundancy case) in depth
- Proved **B-all-redundancy from A-all-redundancy**: if every x ∈ A+B has ≥ 2 A-reps (hrep2),
  then ∀ b ∈ B, A+(B\{b}) = A+B. Proof: if x ∉ A+(B\{b₀}), all reps of x use b₀ → at most 1 rep,
  contradicting hrep2. (~10-15 lines in Lean, using hrep2 already proved at lines 782-804)
- Attempted orbit argument via B-all-redundancy: for |A|=2, B is closed under a fixed shift d=a₁-a₀,
  giving |B| ≥ p. But for |A| ≥ 3, the shift d varies with b — no fixed d.
- Verified for |A|=4, |B|=3: hineq gives equality 12 = 2*6, so every element has EXACTLY rep = 2
  (the counting is tight). Bipartite graph analysis shows no immediate contradiction from rep = 2.
- Confirmed the Aristotle companion file (lines 258-265) acknowledges the same blocker.

### Key Findings

- **B-all-redundancy derivation** (elementary, ~15 Lean lines): From `hrep2` (rep_A(x) ≥ 2 for all
  x ∈ A+B), B is also all-redundant: ∀ b ∈ B, A+(B\{b}) = A+B. The companion file already has
  this at lines 145-162 via `non_redundant_b_gives_a`. Can be added to main file.
- **Orbit argument barrier**: The |B|=2 orbit argument works because A is closed under the UNIQUE
  nonzero difference d of B (forced by |B|=2). For |B|≥3 and |A|≥3, B-all-redundancy gives: ∀ b ∈ B,
  ∃ d ∈ (A-A)\{0}: b+d ∈ B. But d varies with b — can't apply orbit argument.
- **tight rep=2 case** (|A|=4, |B|=3): Counting is exactly tight: 4*3=12=2*6. So rep_A(x)=2 exactly
  for all x. Bipartite graph is 3-regular (A-side) and 2-regular ((A+B)-side). No immediate
  arithmetic contradiction found.
- **Assessment: BLOCKED** — The sorry at line 844 requires either (1) Kneser's theorem ~200-300 lines,
  (2) a polynomial/Fourier approach (~100+ lines), or (3) complete proof restructuring.

### Files Modified

- None (analysis only)

### Next Steps

1. **Build B-all-redundancy into main proof** (~15 lines, easy): Add `hredB_eq` after `hredA_eq`
   in the sorry block. Gives more hypotheses for future attempts.
2. **Kneser build**: For ZMod p, Kneser reduces to CD (trivial subgroups), but the STRUCTURAL
   application differs. The "Kneser route" for Vosper is: use Kneser to show all-redundant A
   forces A+B to be a coset (impossible in ZMod p with |A+B| < p). Estimated: ~200-300 lines.
3. **Alternative: polynomial method** using combinatorial Nullstellensatz over ZMod p.
4. **Flag as BLOCKED and move on** (3 sessions on this sorry with |A|≥4,|B|≥3 sub-case).

---

## Session 2026-04-25 (Session 2) — Counting Argument: |A|=|B|=3 Sub-case Proved

**Mode**: REVISIT
**Outcome**: progress

### What I Did

- Proved the `|A|=|B|=3` sub-case of the all-redundant contradiction in `Erdos476OQ05Problem.lean`
- Implemented the counting argument: if all of A is redundant (∀ a, A.erase a + B = A + B), then
  every x ∈ A+B has ≥ 2 distinct A-representations (r(x) ≥ 2). Double counting gives
  |A|·|B| ≥ 2·|A+B| = 2(|A|+|B|-1). For |A|=|B|=3: 9 ≥ 10, contradiction.
- Added `hrep2` (r(x) ≥ 2 for x ∈ A+B), `hsum_eq` (sigma bijection double counting), `hlb` (sum lower bound), `hineq` (counting bound)
- The sorry now covers only `|A|≥4 or |B|≥4` (not all of `|B|≥3`)
- Documented that Kneser's theorem is needed for the general case

### Key Findings

- **r(x) ≥ 2 proof**: If only a₁ ∈ A satisfies x-a₁ ∈ B, then x ∉ (A.erase a₁)+B, contradicting the SET equality hredA. Uses `Finset.card_eq_one` + contraposition.
- **Double counting via sigma bijection**: `(A+B).sigma (fun x => A.filter (fun a => x-a ∈ B))` bijects to `A.product B` via `(x, a) ↦ (a, x-a)`. Used `Finset.card_bij` + `Finset.card_sigma` + `Finset.card_product`.
- **Kneser barrier for general case**: For |A|≥4 or |B|≥4, the counting bound (|A|-2)(|B|-2) ≥ 2 is SATISFIED (not contradicted), so the counting argument gives no contradiction. Kneser's theorem is needed to derive that full redundancy forces a periodic structure — Kneser is NOT in Mathlib.
- **Key Lean tactics**: `eq_sub_of_add_eq`, `sub_add_cancel`, `obtain rfl :=`, `congr_arg`

### Files Modified

- `proofs/Proofs/Erdos476OQ05Problem.lean` (809 → 874 lines)
  - Lines 777-843: replaced single sorry with counting argument (~65 lines)
  - `|A|=|B|=3` sub-case proved
  - Still 1 sorry at line 843 for `|A|≥4 or |B|≥4`

### Next Steps

1. **Kneser's theorem**: The remaining sorry needs Kneser. Not in Mathlib. Would require ~200-300 lines of infrastructure. Assessment: BUILD is feasible but high-effort.
2. **Alternative approach (Schur-like)**: Try Freiman's theorem for the case |A+B|=|A|+|B|-1. May have a more elementary proof path.
3. **Submit `case1_exists` to Aristotle**: The Aristotle companion has a cleaner version of this lemma. Aristotle might fill in the counting argument part if the infrastructure is right.

---

## Problem Understanding

**Goal**: Fill the remaining sorry in `Erdos476OQ05Problem.lean` to complete Vosper's theorem.

### The Two Sorries

**SORRY 1** (line 166, `vosper_induction`):
```lean
-- Key step: position analysis forces |A \ A.image(·+d)| = 1
sorry
```
The inductive hypothesis gives `|A + B| = |A| + |B| - 1`. If A isn't a singleton,
then for any shift d ∈ B - B, the set `A \ A.image(·+d)` must have cardinality 1.
This follows from: if |A ∩ A.image(·+d)| = |A| - 1, then by `ap_of_near_periodic`,
A is an AP. The counting argument uses Finset inclusion-exclusion.

**SORRY 2** (line 407, main case analysis):
```lean
-- Case 1 existence: counting argument or iterative removal
sorry
```
Need to exhibit a specific `d` such that the shift argument works. In the literature
proof, this is done by taking d to be the common difference of B (which is an AP
by induction hypothesis).

### Proof Strategy (Literature)

The standard proof of Vosper (1956) proceeds:
1. Fix d = common difference of B (by induction, B is an AP)
2. Show A + {d} intersects A in exactly |A|-1 elements (Cauchy-Davenport equality forces this)
3. Apply `ap_of_near_periodic` to conclude A is an AP with difference d

### Key Lean Infrastructure (Already Proved)

- `ap_of_near_periodic`: if `A \ A.image(·+d) = {x}` (singleton), then A is an AP
- `vosper_base`: |A| = 2 case is closed
- `IsArithmeticProgression p d A`: defined as consecutive shifts of a base element
- `ap_iff_card_inter`: A is AP iff `|A ∩ A.image(·+d)| = |A| - 1`

---

## Insights

### Finset API Requirements

For SORRY 1, the key lemmas needed:
- `Finset.card_sdiff` : `B ⊆ A → |A \ B| = |A| - |B|`
- `Finset.card_image_of_injective` : `|A.image f| = |A|` if f injective
- `Finset.card_union_add_card_inter` : inclusion-exclusion

For SORRY 2:
- Existence of d from the AP structure of B (inductive hypothesis)
- `Finset.card_le_card` for comparison arguments

### Aristotle Eligibility

Both sorries are **theorem sorries** (not def sorries) — Aristotle-eligible.
The companion file `Erdos476OQ05Aristotle.lean` exists and exposes these as standalone
theorems. Recommend Aristotle submission as first approach.

---

## Dead Ends

- **Counting argument for |A|≥4, |B|≥3**: Double counting gives hineq (|A|-2)(|B|-2) ≥ 2 which
  HOLDS (not contradicted) for all such cases. The counting approach is exhausted.
- **Orbit argument via B-all-redundancy**: B-all-redundancy gives ∀ b ∈ B, ∃ d ∈ (A-A)\{0}: b+d ∈ B.
  But d varies with b (no fixed d), so the orbit/periodicity argument doesn't apply for |A| ≥ 3.
- **Iterative element removal**: A being all-redundant (removing any a preserves A+B) does NOT imply
  that A\{a} is also all-redundant. Cannot iterate removal to reach |A|=2.
- **Inductive hypothesis (IH) application**: (A\{a₀}, B) with all-redundant A has |(A\{a₀})+B| =
  |A|+|B|-1 > |A\{a₀}|+|B|-1, so Vosper equality condition fails. IH doesn't apply.
- **IH via B-perspective**: Symmetric argument. (A, B\{b₀}) with B all-redundant has same issue.
