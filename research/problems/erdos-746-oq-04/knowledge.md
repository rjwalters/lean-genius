# Knowledge Base: erdos-746-oq-04

**Problem**: Prove hamiltonian_implies_connected (Hamiltonian cycle implies connectivity)
**Phase**: ACT

---

## Problem Understanding

The file `Erdos746Problem.lean` formalizes Erdős #746 (random graph Hamiltonicity threshold).
OQ-04 targets the `hamiltonian_implies_connected` theorem: a Hamiltonian graph is connected.

The theorem was already written but had 2 sorries embedded in `IsHamiltonianCycle` definition.

---

## Session 2026-04-02 (Session 1) - Fix Definition Sorries

**Mode**: FRESH
**Outcome**: progress — 2 sorries eliminated in `IsHamiltonianCycle`, sorry count 3→1

### What I Did

- Identified that `IsHamiltonianCycle` had 2 sorries in the closing arc condition:
  ```lean
  (n > 0 → G.Adj (cycle.getLast (by sorry)) (cycle.head (by sorry)))
  ```
  The `by sorry` proved `cycle ≠ []`, which is unavailable at definition time.

- Fixed by replacing `getLast`/`head` with index-based access:
  ```lean
  (∀ hn : 0 < cycle.length, G.Adj (cycle.get ⟨cycle.length - 1, by omega⟩) (cycle.get ⟨0, hn⟩))
  ```
  `by omega` closes `cycle.length - 1 < cycle.length` from `hn : 0 < cycle.length` in scope.
  The `∀ hn` change is mathematically equivalent: an empty cycle (length=0) trivially satisfies
  the new form, just as `n > 0 →` was vacuous for non-Hamiltonian inputs.

- The proof of `hamiltonian_implies_connected` destructs this component as `_`, so no proof changes needed.

### Key Findings

- Definition sorries in `Prop`-returning `def`: `by sorry` proves a proof term embedded in
  the Prop value. These sorries add axiom dependencies to ALL theorems using the definition.
- Index-based access via `cycle.get ⟨i, h⟩` avoids needing `cycle ≠ []` at definition time —
  just add the non-emptiness as a hypothesis (`∀ hn : 0 < cycle.length, ...`).
- `erdos_746_answer` sorry (Korshunov/Komlós-Szemerédi 1983) is a deep theorem requiring
  ~1000+ lines of probabilistic combinatorics — effectively blocked.

### Files Modified

- `proofs/Proofs/Erdos746Problem.lean` line 90: fixed 2 definition sorries

### Next Steps

- `erdos_746_answer` is effectively BLOCKED (requires formalizing Korshunov's theorem)

---

## Insights

- `IsHamiltonianCycle` definition: use `∀ hn : 0 < cycle.length, ...` instead of `n > 0 →`
  combined with `getLast`/`head` — avoids inline sorry for non-emptiness
- Closing arc reformulation: `cycle.get ⟨cycle.length-1, by omega⟩` and `cycle.get ⟨0, hn⟩`

## Dead Ends

- Trying to prove `cycle ≠ []` inline in the definition: not possible without earlier conjuncts
