# Problem: Density Increment via Gowers Norms

**Slug**: roth-theorem-k3-oq-03-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\|f\|_{U^3} \geq \delta \Rightarrow \exists \text{ density increment on progression}
$$

### Plain Language

Generalization of Roth density increment to k-APs using Gowers uniformity norms. Gowers norms and k-AP counting operator defined. 1 sorry + 2 axioms for the main estimate.

### Why This Matters

See `src/data/proofs/roth-theorem-k3-oq-03/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `roth-theorem-k3-oq-03` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

For k=3, the density increment from U^2 norms follows from Roth infrastructure. Check if the existing RothTheorem.lean results can be directly applied via Fourier inversion.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `roth-theorem-k3-oq-03` | Direct parent — inspect its Lean file for sorry locations |

## Must Prove Exactly / Does Not Count

**Target (as scoped at S2 ORIENT, Approach A)**: the exact k = 3 instance of the
parent axiom `RothTheoremOQ03.density_increment_kAP`, proved without using the
axiom:

```
∀ (N : ℕ) [NeZero N], N ≥ 2 → ∀ (A : Finset (ZMod N)) (δ : ℝ),
  δ = A.card / N → 0 < δ → IsKAPFreeZMod A 3 →
  ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
    ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
      δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' 3
```

**Does not count**:
- Restating `density_increment_k3_explicit` under a new name without matching
  the axiom's exact conclusion shape (`δ' > δ`, the two anonymous `∃ _ : _`
  binders, conjunction order).
- Any derivation that (transitively) uses `density_increment_kAP` itself or
  `Szemeredi.szemeredi_k_ge_4` — must be certified by `#print axioms`.
- Discharging the general-k axiom (k ≥ 4) is NOT required — it needs the Gowers
  U^{k-1} inverse theorem and is out of scope for this node.

## Adversarial Checklist (S6 SOLVED claim, 2026-07-23)

1. **Statement mismatch vs the axiom**: confirm `density_increment_kAP_k3` in
   `Proofs/RothTheoremK3OQ03Incomplete01.lean:44` matches the axiom at
   `Proofs/RothTheoremOQ03.lean:304` instantiated at `k := 3` — same hypothesis
   list (`[NeZero N]`, `N ≥ 2`, `δ = A.card / N`, `0 < δ`,
   `IsKAPFreeZMod A 3`; `hk : 3 ≥ 3` discharged trivially) and identical
   conclusion including the anonymous binders `(_ : 0 < M) (_ : M < N)` and the
   conjunct order `δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' 3`.
2. **Circularity**: the proof must not use the axiom it discharges. Certified:
   `#print axioms density_increment_kAP_k3` (in-file, line 84) reports only
   `[propext, Classical.choice, Quot.sound]` in the 2026-07-23 docker build log
   — neither `density_increment_kAP` nor `szemeredi_k_ge_4` appears.
3. **Near-miss (weaker density conclusion)**: the axiom demands strict `δ' > δ`;
   the source lemma gives `δ' ≥ δ + δ²/100`. The bridge must derive strictness
   from `0 < δ` (if `δ = 0` were allowed, `δ²/100 = 0` and strictness fails) —
   hypothesis `hδ_pos` is genuinely load-bearing.
4. **Degenerate moduli**: the conclusion's `0 < M` and `M < N` come through
   unchanged from `density_increment_k3_explicit`; nothing in the bridge relaxes
   them (M = 0 or M = N would trivialize the increment).
5. **AP-free preservation**: `IsKAPFreeZMod A' 3` (not merely 3-AP-freeness of
   some unrelated set) is passed through from the source lemma — without it the
   increment cannot iterate, and a proof dropping it would be a wrong-statement
   near-miss.
6. **Scope honesty**: this discharges only k = 3. The parent axiom remains for
   k ≥ 4 and the parent entry remains `axiomatized`; only this node's companion
   file is axiom-free.

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - combinatorics
  - gowers-norms
  - additive-combinatorics
  - density-increment
related_proofs:
  - roth-theorem-k3-oq-03
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 5/10
