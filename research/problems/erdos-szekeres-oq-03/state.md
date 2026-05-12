# Current State

**Phase**: ORIENT
**Since**: 2026-05-12 (S1 OBSERVE → ORIENT, researcher-8)
**Iteration**: 1

## Current Focus

Session 1 (S1, researcher-8, 2026-05-12): Survey of the hypergraph
Ramsey-number literature for the OQ-03 generalization of Erdős–Szekeres.
No Lean changes — pure OBSERVE/ORIENT pass to set up future ACT sessions.

Output of this session:

* `problem.md` — formal restatement of OQ-03 as three sub-goals
  (existence OQ-03a, Erdős–Rado upper bound OQ-03b, Erdős–Hajnal lower bound
  OQ-03c) with explicit tower-function bounds.
* `knowledge.md` — literature survey covering Ramsey (1930), Erdős–Rado
  (1952), Erdős–Hajnal (1972) stepping-up, and Conlon–Fox–Sudakov (2010);
  Mathlib API audit; suggested `RamseyK.ramseyNumber` API surface.
* This `state.md` update advancing NEW → ORIENT and pinning the
  S2 next-action.

## Active Approach

Three-step Lean formalization plan (S2 → S4):

1. **S2 (ACT-A).** Define `RamseyK.IsRamsey n k s t` and
   `RamseyK.ramseyNumber k s t`. Prove the `k = 1` sanity check
   `ramseyNumber 1 s t = s + t - 1` via pigeonhole (~30 lines of Lean,
   no new Mathlib dependencies). State `ramsey_existence` as a sorry.
2. **S3 (ACT-B).** Discharge `ramsey_existence` via the two-layer
   neighborhood induction. Base case `k = 2` reuses
   `SimpleGraph.ramseyNumber`'s existence proof (or re-proves it inline
   using pigeonhole). Inductive step uses the "fix a vertex, induct on
   `(k-1)`-coloring of neighborhood" construction.
3. **S4 (ACT-C).** State `erdos_rado_upper` as `ramseyNumber k s s ≤
   tower (k-1) (c_k * s)`. Likely needs an explicit `c_k` (e.g.
   `c_k = 4 * (k-1)!`); the tower function can be defined via
   `Nat.iterate (2 ^ ·) (k-1) (c_k * s)` so no new tower API.
   Proof: follow the Erdős–Rado recursive bound
   `R_k(s,t) ≤ R_{k-1}(R_k(s-1,t), R_k(s,t-1)) + 1`, unwound.

S5+ would tackle the stepping-up lower bound (OQ-03c), but only after S4
lands. The lower bound is harder and may need its own sub-OQ.

## Blockers

None for S2 (definitions are straightforward Mathlib boilerplate).

For S3/S4: `Hypergraph` is not yet in Mathlib, so we work directly with
`Finset (Fin n)` filtered by `card = k` (`Finset.powersetCard`). This is
adequate but verbose.

## Next Action

**S2 ACT-A.** Create `proofs/Proofs/RamseyHypergraph.lean` with:

* `def IsMonochromatic {n k : ℕ} (χ : Finset (Fin n) → Bool) (S : Finset (Fin n)) (c : Bool) : Prop`
* `def IsRamsey (n k s t : ℕ) : Prop`
* `def ramseyNumber (k s t : ℕ) : ℕ := Nat.find ...`
* `lemma ramseyNumber_one (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) : ramseyNumber 1 s t = s + t - 1`
* `theorem ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t) : ∃ n, IsRamsey n k s t := by sorry`

Add the gallery shim: `src/data/research/problems/erdos-szekeres-oq-03.json`
should list this new file under `leanFiles` (or leave unchanged if the
file is not yet created; S2 will add the entry).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (literature survey + Lean API design)

## Outcome of S1

ORIENT complete. Three sub-goals (existence, Erdős–Rado upper, Erdős–Hajnal
lower) cleanly stated; Mathlib gaps identified; S2 ACT-A is unblocked.
