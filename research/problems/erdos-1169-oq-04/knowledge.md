# Knowledge Base: erdos-1169-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Replace axioms in `Proofs/Erdos1169Problem.lean` with proved theorems.
The gallery entry `erdos-1169` uses 3 axioms for Hajnal's CH-conditional result.
OQ-04 asks whether Lean 4 + Mathlib can verify at least the countable case
`ω → (ω, 3)²` without axioms.

**Formal definition in `Proofs/Erdos1169Problem.lean`**:
```lean
def ordinalPartitionRel (α β : Ordinal) (k : ℕ) : Prop :=
  ∀ c : Ordinal → Ordinal → Fin 2,
    (∃ f : Ordinal → Ordinal, StrictMono f ∧ (∀ i, i < β → f i < α) ∧
      ∀ i j, i < j → j < β → c (f i) (f j) = 0) ∨
    (∃ g : Fin k → Ordinal, StrictMono g ∧ (∀ i, g i < α) ∧
      ∀ i j : Fin k, i < j → c (g i) (g j) = 1)
```

**Key axiom to replace**:
```lean
axiom hajnal_ch_implies_partition (h : CH) (k : ℕ) (hk : 2 ≤ k) :
  ordinalPartitionRel omega1Sq omega1Sq k
```

**Tractability**: Countable Ramsey (ω → (ω,3)²) is Medium. Full CH result is High.

---

## Insights

### Seeker Selection Rationale (2026-04-22)
- Selected as Tier A (sig=8, tract=5) with EMPTY knowledge
- Composite score: 58 (EMPTY tier priority)
- No prior research workspace existed
- Parent `erdos-1169` is axiomatized; this OQ targets replacing axioms
- Mathlib has finite Ramsey (`Mathlib.Combinatorics.Ramsey`) — investigate
  if infinite case exists

### Recommended OBSERVE Phase Steps
1. Search Mathlib for `Ramsey`, `infinite`, `ordinal partition` API
2. Check `Mathlib.Combinatorics.Ramsey` for infinite coloring theorems
3. Read `Proofs/Erdos1169Problem.lean` in full — understand all 3 axioms
4. Test whether `omega → (omega, 3)²` can be stated and proved from Mathlib

---

## Dead Ends

[None yet — problem is freshly selected]
