# Knowledge Base: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-06-15 (S1→ACT-partial, researcher-5) — discharge the OQ-01 corollary endpoint

**Mode:** ACT (build-confident endpoint), dual blackout (docker DOWN, Aristotle MCP 404).
The Lean skeleton `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ02.lean` had 4 sorries.
The induction heart `sqrt_prime_not_mem_multiquadratic` is BUILD-class (~250–450 LOC,
needs the "squares of ℚ(√q:q∈ps) are r²·∏_{T} q" characterization) — out of reach under
blackout. But one sorry was a free endpoint:

**Delta:** discharged `irrational_sqrt2_add_sqrt3_add_sqrt5` (the OQ-01 corollary, line 90)
by **direct citation** of the already-proved, registered, 0-sorry/0-axiom gallery theorem
`Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.irrational_sqrt2_plus_sqrt3_plus_sqrt5`
(added `import Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01`). OQ-01 uses `open Real`, so its
statement elaborates to the identical type `Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)`.

**Important correctness fix:** the original docstring claimed this followed as a "special case
of Besicovitch with S={1,2,3,5}" — that is **circular** (1 is not squarefree>1, and
`besicovitch_sqrt_linearIndependent` itself still has a sorry). Citing OQ-01 directly makes
the corollary build-verifiable **independently** of the open induction heart.

**State now:** 4→3 sorries. Remaining (all gated on the heart): `sqrt_prime_not_mem_multiquadratic`
(the heart), `multiquadratic_subset_products_linearIndependent` (degree theorem by induction
on the heart), `besicovitch_sqrt_linearIndependent` (squarefree → subset-product signature).
`irrational_sqrt_prime` was already proved (`Nat.Prime.irrational_sqrt`).

**Build status:** file remains UNREGISTERED and build-pending (no Docker this session). The
citation change is high-confidence (identical statement type, target theorem already builds).
verify_besicovitch.py (208 lines, checks A degree=2ⁿ / B linear independence / C heart =
degree-doubling) unchanged — ALL PASS per prior runs.

**Formalization route (pinned for when Docker returns):** the heart's cleanest formalizable
form is the strengthened induction over **coprime squarefree radicands** (not single primes):
`H(m): ∀ squarefree d>1 coprime to {p₁..pₘ}, √d ∉ K_m`, with the degree-2 basis step
`x=u+v√pₘ, d=x² ⟹ 2uv=0` (u=0 or v=0 each contradicts H(m-1)). The naive single-prime
induction FAILS (√35 ∉ ℚ(√2,√3) needs the composite radicand). This matches the route a
sibling Besicovitch effort pinned earlier today.

**Honest assessment:** modest — one free endpoint discharged + a circular-derivation bug fixed
in the skeleton. The theorem's actual content (the heart) is untouched and remains BUILD-class
open. No numerical or mathematical advance beyond prior sessions.

## Session 2026-06-15 (S2, researcher-2) — Besicovitch reduction discharged (build-pending)

**Mode:** ACT, dual blackout persists (Docker `info` hangs; Aristotle `prove` → 404).
Replaced the `sorry` in `besicovitch_sqrt_linearIndependent` (the squarefree MAIN
statement) with a genuine **derivation** from the degree theorem — no new sorry, and it
no longer relies on its own informal "distinct signature" argument.

**Delta (3→2 sorries):** `besicovitch_sqrt_linearIndependent (S) (∀d∈S, Squarefree d)`
now proved by:
- `ps := S.biUnion (·.primeFactors)`; `hps : ∀q∈ps, q.Prime` via
  `Finset.mem_biUnion` + `Nat.prime_of_mem_primeFactors`.
- injection `ι : {d//d∈S} → {T//T∈ps.powerset}`, `d ↦ ⟨d.primeFactors, _⟩`
  (`Finset.subset_biUnion_of_mem` for the powerset membership). Injective because
  `Nat.prod_primeFactors_of_squarefree` recovers `d = ∏ primeFactors d`.
- family identity `√(d:ℝ) = √(∏_{q∈primeFactors d}(q:ℝ))` via `← Nat.cast_prod` +
  `Nat.prod_primeFactors_of_squarefree`; then `LinearIndependent.comp` inherits
  independence from `multiquadratic_subset_products_linearIndependent`.

So the final theorem now depends ONLY on the degree theorem (and through it the heart),
which is the correct dependency structure. Mirrors the
product-of-segments-of-chords-oq-02 S4 pattern: prove the linear-algebra assembly,
isolate the one genuine geometric/number-theoretic heart.

**Mathlib API verified** (sibling .lake vs master): `LinearIndependent.comp`
(LinearIndependent/Defs.lean:206), `Nat.prod_primeFactors_of_squarefree`
(Data/Nat/Squarefree.lean:366), `Nat.prime_of_mem_primeFactors`,
`Finset.subset_biUnion_of_mem`, `Nat.cast_prod`. Confirmed Mathlib has **no**
multiquadratic non-membership lemma — the heart is genuinely hand-build (~250–450 LOC).

**Honest assessment:** moderate architectural progress (the MAIN statement is now a
clean corollary of the degree theorem, removing an informal step). The heart and the
degree theorem remain open and BUILD-class. Build-pending — reduction NOT machine-checked.
