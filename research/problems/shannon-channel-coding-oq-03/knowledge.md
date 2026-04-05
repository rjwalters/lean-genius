# Knowledge Base: shannon-channel-coding-oq-03

## Problem Summary

**Fano's Inequality**: For a joint distribution P_{XY} on finite alphabets with |X| ≥ 2:

$$H(X|Y) \leq h(P_e) + P_e \cdot \log(|X| - 1)$$

where P_e = 1 - ∑_y ∑_x P(x,y)²/P(Y=y) (gallery formula) and h is binary entropy.

**Target**: Replace the `fano_inequality` axiom in `ShannonChannelCoding.lean`.

---

## Session 2026-04-04 (Session 1)

**Mode**: FRESH
**Outcome**: progress — proof architecture complete, 5 sorries remain

### What I Did

- Created `proofs/Proofs/ShannonChannelCodingOQ03.lean` (self-contained, 255 lines)
- Proved `sum_sq_le_max`: ∑q(x)² ≤ max q(x) for probability distributions
- Proved `formula_pe_ge_map_pe`: MAP P_e ≤ gallery formula P_e
- Established full proof architecture connecting all components to main theorem
- Built passes (6 sorry warnings)
- Created gallery data in `src/data/proofs/shannon-channel-coding-oq-03/`
- Discovered ShannonEntropy.lean has pre-existing build issue (strong_subadditivity)

### Key Findings

- **Two error probability definitions**: gallery uses formula P_e = 1 - ∑P²/P(Y), classical MAP = 1 - ∑max P. They differ but MAP ≤ formula (proved).
- **Core algebraic key**: ∑q² ≤ max(q) follows immediately from q(x) ≤ max(q) and summing.
- **Bimodal reference** for Gibbs in per-element Fano: Q(x*) = p* = max(q), Q(x) = (1-p*)/(n-1) elsewhere. Yields exactly h(p*) + (1-p*)·log(n-1).
- **Jensen for h** (concave, proved in OQ04) aggregates per-slice bounds into joint bound.
- **Monotonicity** of h(p) + p·log(c): derivative = log((1-p)c/p) ≥ 0 on [0, c/(1+c)].
- **Workaround needed**: ShannonEntropy.lean fails at line 811 (strong_subadditivity linarith). Made OQ03 self-contained, importing only Mathlib + OQ04.

### Files Created/Modified

- `proofs/Proofs/ShannonChannelCodingOQ03.lean` (created, 255 lines)
- `src/data/proofs/shannon-channel-coding-oq-03/meta.json` (created)
- `src/data/proofs/shannon-channel-coding-oq-03/annotations.json` (created)
- `src/data/proofs/shannon-channel-coding-oq-03/index.ts` (created)
- `src/data/research/problems/shannon-channel-coding-oq-03.json` (updated with progress)
- `proofs/Proofs/ShannonEntropy.lean` (partial fixes: lines 638, 735; line 811 still broken)

### Remaining Sorries (in order of effort)

1. **`gibbs_inequality`** (sorry): Follows from Real.log_le_sub_one_of_pos. Should be ~15 lines.
2. **`slice_sq_le_max`** (sorry): Normalize to conditional q_y(x) = P(x,y)/P(Y=y), apply sum_sq_le_max. ~20 lines.
3. **`fano_per_element`** (sorry): Gibbs + bimodal reference Q + h symmetry. ~30 lines.
4. **`fano_map_bound`** (sorry): Decompose H(X|Y), apply per-element, Jensen for h. ~40 lines.
5. **`fano_func_mono`** (sorry): Monotonicity of h(p)+p·log(c). Calculus, ~20 lines.

### Next Steps

1. Attempt gibbs_inequality first — it's the foundation and is a known result
2. Then slice_sq_le_max — straightforward algebra once gibbs is done
3. Consider submitting fano_map_bound to Aristotle (Jensen step is formulaic)
4. Investigate ShannonEntropy.lean line 811 separately (pre-existing, not blocking OQ03)

---

## Insights

- Gallery formula P_e and MAP P_e are distinct: formula is computed from ∑P²/P(Y), MAP from ∑max P
- The ≤ direction (MAP ≤ formula) holds by Cauchy-Schwarz / ∑q² ≤ max(q)
- h(p) symmetry h(p) = h(1-p) is key in per-element Fano for the mode case
- Making OQ03 self-contained avoids the ShannonEntropy dependency chain issue

## Dead Ends

- Importing Proofs.ShannonEntropy: fails due to strong_subadditivity build error at line 811
- Trying to fix ShannonEntropy line 811 during this session: deprioritized as unrelated to OQ03

## Mathlib Gaps

- Gibbs inequality not directly in Mathlib (must derive from log(x) ≤ x-1)
- No per-element Fano bound in Mathlib
- ConcaveOn.smul_le_sum exists but needs careful instantiation for Jensen step
