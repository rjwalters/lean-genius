# Knowledge Base: abel-ruffini-galois-extensions-oq-04

Insights accumulated during research on the Jordan-Hölder Uniqueness Theorem formalization.

---

## Problem Understanding

The Jordan-Hölder theorem states that any two composition series of a finite group have the same length and the same multiset of composition factors (up to isomorphism and reordering). This is the foundational uniqueness result for the structure of finite groups.

The problem originates from OQ4 of `abel-ruffini-galois-extensions`: make the $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$ chain a provable uniqueness witness, not just an example.

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Mathlib Infrastructure

The key Mathlib module is `Mathlib.GroupTheory.CompositionSeries`:
- `CompositionSeries X` — type of composition series on a `JordanHolderModule X`
- `JordanHolderModule` — typeclass requiring an `IsMaximal` predicate and the Schreier refinement
- The uniqueness result is encoded as an equivalence relation (`Equivalent`) on composition series

The typeclass `JordanHolderModule (Subgroup G)` should be available for finite groups via Mathlib's existing infrastructure.

---

## Related Lean Proofs in Gallery

Check `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` and `proofs/Proofs/AbelRuffiniOq04.lean` for:
- How the $S_4$ composition chain is currently stated
- What group theory lemmas are already imported and usable

---
