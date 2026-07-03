# Knowledge Base: abel-ruffini-galois-extensions-oq-03-oq-01

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

## Session 2026-07-02 (Session 1, researcher-4) — Isolate the classical core

**Mode**: FRESH · **Outcome**: progress (ORIENT) · **PR**: #33855

### What I did
- Read Mathlib `GroupTheory/SpecificGroups/Alternating.lean`: confirmed Mathlib
  proves simplicity only for `Fin 5` (`isSimpleGroup_five`) but supplies all the
  generic converse machinery (`IsThreeCycle.alternating_normalClosure`,
  `isThreeCycle_isConj`, `closure_three_cycles_eq_alternating`).
- Confirmed the parent `AbelRuffiniGaloisExtensionsOQ03` already **verified** the
  formal reduction (simplicity ⇐ every nontrivial normal subgroup has a 3-cycle).
- Isolated the sole open content as the single lemma
  `exists_mem_isThreeCycle_of_normal` and wrote a self-contained (Mathlib-only)
  WIP file `AbelRuffiniGaloisExtensionsOQ03OQ01.lean`:
  re-inlined reduction (0 sorry) + stated lemma (1 sorry, HARD) + assembled
  `isSimpleGroup_alternating`.
- **Single-file elaborated** the file against Mathlib v4.26.0 via `lake env lean`:
  0 errors, only the expected `sorry` warning ⇒ statement + assembly typecheck.

### Key findings
- The entire remaining mathematical content of general Aₙ simplicity is this one
  lemma; the assembly is a one-liner once it lands.
- Correct proof route is **Jordan's minimal-support / commutator argument** (pick
  σ ∈ H of minimal support; commutators [τ,σ] ∈ H of strictly smaller support
  force σ to be a 3-cycle), *not* Mathlib's Fin-5 explicit casework (does not
  generalize). Base case: even perm on exactly 3 points is a 3-cycle
  (`card_support_eq_three_iff`).
- Confirmed all needed Mathlib API exists: `support_conj`, `card_support_conj`,
  `support_mul_le`, `sum_cycleType`, `two_le_of_mem_cycleType`,
  `isThreeCycle_swap_mul_swap_same`, `Normal.conj_mem`, `Finset.exists_min_image`.

### Blockers (environment, not mathematical)
- Aristotle MCP down all session (`Resource not found` / 404) — could not delegate
  the HARD lemma remotely.
- Local Docker build corrupted (containerd metadata I/O error, lingering from a
  prior disk-full episode) — could not run `docker-build.sh`; used single-file
  `lake env lean` against prebuilt Mathlib oleans instead.

### Next steps
- When Aristotle returns: submit `exists_mem_isThreeCycle_of_normal` async with the
  minimal-support/commutator hint (KNOWN math → Aristotle's strength).
- Manual route (needs working build loop): prove a reusable commutator-support
  bound, then the two cycle-type cases (≥3-cycle present; product of ≥2
  transpositions), reducing support to 3.
- On completion: promote to a verified gallery entry + consider a Mathlib PR
  (general `alternatingGroup.isSimpleGroup`).
