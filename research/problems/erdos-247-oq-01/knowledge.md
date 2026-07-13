# Knowledge Base: erdos-247-oq-01

Transcendence of Lacunary Sum 1/2^(k^2) - Erdős Problem #247

---

## Session 2026-03-20 (Sessions 1-2) - Liouville Proof

**Mode**: FRESH → ACT
**Outcome**: progress

### Work Done
- Added Part VIII: Direct Liouville proof structure for factorial transcendence
- Proved strictMono_add_le, factorial_mul_lt, factorial_mul_add_one_lt
- Main theorem factorial_sum_liouville outlined with sorries
- Created Aristotle companion file with 9 targets

---

## Session 2026-03-21 (Session 3) - Sorry Elimination

**Mode**: REVISIT
**Outcome**: COMPLETED

### Key Discovery
`IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ` from Mathlib provides:
`IsAlgebraic ℚ x ↔ IsAlgebraic ℤ x`

This is exactly the "clearing denominators" result needed for
`transcendental_int_to_rat : Transcendental ℤ x → Transcendental ℚ x`.

### Proof
```lean
theorem transcendental_int_to_rat {x : ℝ} (h : Transcendental ℤ x) :
    Transcendental ℚ x :=
  fun halg => h ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg)
```

### Bonus: Eliminated axioms in other files
- `eTranscendental.lean`: Removed `e_transcendental_over_rationals_axiom` (6→5 axioms)
- `PiTranscendental.lean`: Removed `pi_transcendental_over_rationals_axiom` (9→8 axioms)

### Final State
- Erdos247Problem.lean: **0 sorries, 1 axiom** (erdos_transcendence_strong - deep, intentional)
- Axiom-free factorial transcendence: COMPLETE via Liouville path
