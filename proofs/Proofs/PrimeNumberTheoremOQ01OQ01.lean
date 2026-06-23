/-
  # Bridge: the two `RiemannHypothesis : Prop` declarations are equivalent

  This file resolves the slug-duplication concern raised in S1 OBSERVE
  (PR #18235) for `prime-number-theorem-oq-01-oq-01`. Two `RiemannHypothesis : Prop`
  declarations exist in the codebase:

  1. `RiemannHypothesis.RiemannHypothesis` in `Proofs/RiemannHypothesis.lean:128`,
     defined via `isNonTrivialZero` (zero ∧ critical-strip packed into a single
     hypothesis):
     ```
     ∀ s, isNonTrivialZero s → s ∈ criticalLine
     ```

  2. `PrimeNumberTheoremOQ01.RiemannHypothesis` in
     `Proofs/PrimeNumberTheoremOQ01.lean:70`, defined with the two hypotheses
     separated:
     ```
     ∀ s, riemannZeta s = 0 → s ∈ criticalStrip → s ∈ criticalLine
     ```

  Both files supply an iff-bridge into the canonical explicit form

  ```
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2
  ```

  via `RiemannHypothesis.RH_alt` (`RiemannHypothesis.lean:132`) and
  `PrimeNumberTheoremOQ01.rh_iff_re_half` (`PrimeNumberTheoremOQ01.lean:74`),
  respectively. The bridge between the two RH declarations is then a single
  `Iff.trans`.

  No new axioms. No sorries.
-/
import Proofs.RiemannHypothesis
import Proofs.PrimeNumberTheoremOQ01

namespace PrimeNumberTheoremOQ01OQ01

/-- **Bridge theorem.** The canonical RH declaration in `Proofs/RiemannHypothesis.lean`
(via `isNonTrivialZero`) is propositionally equivalent to the parent PNT slug's RH
declaration in `Proofs/PrimeNumberTheoremOQ01.lean` (with zero + critical-strip
as separate hypotheses). Both unfold via their respective `iff_re_half` /
`RH_alt` characterisation to the same explicit form

```
∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2
```

so the bridge is a single `Iff.trans`. -/
theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis :=
  RiemannHypothesis.RH_alt.trans PrimeNumberTheoremOQ01.rh_iff_re_half.symm

/-- Symmetric form of the bridge: PNT-side RH ↔ canonical RH. -/
theorem rh_pnt_iff_canonical :
    PrimeNumberTheoremOQ01.RiemannHypothesis ↔ RiemannHypothesis.RiemannHypothesis :=
  rh_canonical_iff_pnt.symm

end PrimeNumberTheoremOQ01OQ01
