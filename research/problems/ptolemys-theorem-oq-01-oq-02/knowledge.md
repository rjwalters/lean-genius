# Knowledge Base: ptolemys-theorem-oq-01-oq-02

## Summary

**Status: COMPLETE** (2026-04-24)

Proved the spherical Ptolemy theorem:
```
sin(d_s(a,c)/2) · sin(d_s(b,d)/2) = sin(d_s(a,b)/2) · sin(d_s(c,d)/2) + sin(d_s(a,d)/2) · sin(d_s(b,c)/2)
```
where d_s(x,y) = arccos(⟨x,y⟩) is the geodesic arc distance on the unit sphere.

File: `proofs/Proofs/PtolemysTheoremOQ01OQ02.lean` (270 lines, 0 sorries, 0 axioms)

---

## Session 2026-04-24 — Complete Proof

### Key Findings

- **Chord-arc identity**: `‖a−b‖ = 2·sin(arccos(⟨a,b⟩)/2)` for unit sphere points in any real inner product space
- **Proof strategy**: Euclidean Ptolemy → chord-arc substitution → divide by 4
- **Factor cancellation**: The factor of 4 cancels cleanly because `‖a‖=‖b‖=1` (unit sphere), unlike the hyperbolic case
- **V as self-torsor**: `SeminormedAddCommGroup.toNormedAddTorsor` gives `NormedAddTorsor V V` automatically
- **linear_combination -(1/4)·h_eucl**: cleanest tactic for proving A = B from 4A = 4B
- **cos²(arccos(c)/2) = (1+c)/2**: derived from `cos_two_mul` + `cos_arccos` via `linarith`

### Key Lemmas

1. `inner_unit_mem_Icc`: Cauchy-Schwarz for unit vectors — `⟨a,b⟩ ∈ [-1,1]`
2. `unit_sphere_chord_via_sin`: Chord-arc identity
3. `spherical_ptolemy`: Main theorem

### Hyperbolic Case Status

Surveyed but not proved. The conformal factors `(1-|x|²)` in the Poincaré disk
hyperbolic chord formula `sinh(d_H(a,b)/2) = |a-b|/√((1-|a|²)(1-|b|²))` do NOT cancel
for interior hyperbolic points (unlike unit sphere where they're all 1).
Infrastructure needed: Poincaré disk metric, Möbius isometries (~800-1200 lines).

### Dead Ends

- **Direct hyperbolic approach**: Conformal factors don't cancel cleanly for general interior points
- **Ideal boundary approach**: Works but degenerates to Euclidean Ptolemy on unit circle (trivial)
