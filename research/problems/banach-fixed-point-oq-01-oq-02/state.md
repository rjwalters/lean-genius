# State: banach-fixed-point-oq-01-oq-02

**Phase:** COMPLETED
**Status:** verified (0 axioms, 0 sorries)
**Lean file:** `proofs/Proofs/BanachPerturbationIdentityOQ01OQ02.lean`
**Last updated:** 2026-06-24

## Proof state

| Theorem | Statement | Status |
|---------|-----------|--------|
| `norm_sub_perturb_ge` | `(1−k)‖x−y‖ ≤ ‖f x − f y‖` | ✅ |
| `perturb_antilipschitz` | `AntilipschitzWith (1−k)⁻¹ (id+g)` | ✅ |
| `perturb_injective` | `Injective (id+g)` | ✅ |
| `perturb_continuous` | `Continuous (id+g)` | ✅ |
| `perturb_surjective` | `Surjective (id+g)` (Banach FP) | ✅ |
| `perturb_bijective` | `Bijective (id+g)` | ✅ |
| `perturbHomeo` | `E ≃ₜ E` | ✅ |
| `symm_lipschitz` | `LipschitzWith (1−k)⁻¹ (id+g)⁻¹` | ✅ |
| `symm_norm_sub_le` | `‖f⁻¹a − f⁻¹b‖ ≤ (1−k)⁻¹‖a−b‖` | ✅ |

Axiom profile (`#print axioms`): `propext, Classical.choice, Quot.sound` only.
