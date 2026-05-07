# Problem: Directed Eulerian Theory (konigsberg-oq-01-oq-02)

Extend the Eulerian circuit characterization to directed graphs. A weakly connected digraph has
an Eulerian circuit iff every vertex has equal in-degree and out-degree; directed analogue of
Königsberg bridges.

**Current status**: ACT — 2 of 5 original axioms remain (Hierholzer sufficiency + path iff).
Hierholzer mathematical infrastructure now ~95% complete: 2 sorries remain
(remove_circuit_balanced L953, euler_path_implies_degree_balance L1007).

---

## Session 2026-05-07 (Session 5) - maxTrail_used_eq + maxTrail_last_exhausted

**Mode**: REVISIT (continuing Sessions 2–4)
**Outcome**: progress — 2 of 4 deferred sorries eliminated (4 → 2)

### What I Did

- Proved `maxTrail_used_eq` (L582 in updated file) by direct strong induction on E.card.
  - Recursive case: `maxTrail E v = v :: maxTrail (E.erase c) c.2` and
    `maxTrailRem E v = maxTrailRem (E.erase c) c.2`.
  - Used `Finset.ext` + IH at (E.erase c, c.2). Forward and backward directions both
    case-split on `x = c` (use step 0) vs `x ∈ E.erase c` (apply IH and shift index by 1).
  - Key fact: `c ∉ maxTrailRem (E.erase c) c.2` follows from `maxTrailRem_subset _ _ ⊆ E.erase c`
    and `Finset.not_mem_erase c E`.
- Proved `maxTrail_last_exhausted` (L687) by direct strong induction on E.card.
  - `last_v` of outer trail equals `last_v` of inner trail (since outer = v :: inner).
  - Case split: `e = c` produces step 0 = c; `e ∈ E.erase c` applies IH at (E.erase c, c.2)
    and shifts index by +1.
  - Base case (no outgoing edges from v): trail = [v], so e ∈ E with e.1 = v contradicts
    the empty-filter hypothesis.
- Updated meta `lineCount` 958 → 1107, `sorryCount` 4 → 2 in
  `src/data/research/problems/konigsberg-oq-01-oq-02.json`.

### Key Findings

- The `let last_v := ...` pattern in `maxTrail_last_exhausted` signature unfolds at use
  sites (`maxTrail_closed` consumer); proof terms work because `Fin n` proof-component is
  `Prop` and hence proof-irrelevant.
- `Prod.ext (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b` — direction matters: for `(v, c.2) = c`
  with `c = (c.1, c.2)`, use `Prod.ext hc_v.symm rfl` where `hc_v : c.1 = v`.
- `simp only [hmtail, List.length_cons]; omega` is the standard idiom for length goals
  after `hmtail : maxTrail E v = v :: inner`.
- `simp only [hmtail, List.get_cons_zero, List.get_cons_succ, hinner_start]` reduces
  trail-step expressions to plain `c` values via head/tail decomposition.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (958 → 1107 lines, sorries 4 → 2)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (knowledge updated)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this session appended)

### What Remains

- **`remove_circuit_balanced` (L953)**: removing a directed circuit's edge set preserves
  IsEulerianBalanced. Proof outline: for each vertex v, the edges of C visit v the same
  number of times as a source (from `closed_walk_balance` applied to C.walk) and as a target,
  so inDegree/outDegree both decrease by the same amount. Needs Finset sdiff/filter
  distributivity API and a careful definition of "visits as source/target".
- **`euler_path_implies_degree_balance` (L1007)**: necessity for Eulerian paths. Strengthen
  `HasEulerianPath` with `ExistsUnique` coverage, then apply
  `open_walk_first_source_excess` + `open_walk_last_target_excess` (already proved) plus
  `closed_walk_balance` for interior vertices.
- The two remaining axioms (`directed_eulerian_iff`, `directed_euler_path_iff`) require
  Hierholzer circuit-splicing for the sufficiency directions.

### Next Steps

1. `remove_circuit_balanced`: define helper count `circuitVisits C v = #{i < C.length : C[i] = v}`,
   apply `closed_walk_balance` to `C.walk` to show `circuitVisits = #{i : C[i+1] = v}`.
   Then `outDegree (G.removeEdgeSet ...) v = outDegree G v - circuitVisits` and similarly for
   inDegree, with `IsEulerianBalanced G v` giving the conclusion.
2. Refactor `HasEulerianPath` to use `∃!` instead of `∃`, mirroring `HasEulerianCircuit`.
3. After both sorries are proved: only Hierholzer splicing remains for `directed_eulerian_iff`.

---

## Session 2026-05-03 (Session 3) - Hierholzer Infrastructure

**Mode**: FRESH (continued from Session 2)
**Outcome**: progress — added 478 lines of Hierholzer proof infrastructure, `maxTrail_closed` proved

### What I Did

- Added Part VII: HierholzerInfrastructure section (~478 lines) to KonigsbergOQ01OQ02.lean
- Proved `open_walk_last_target_excess` and `open_walk_first_source_excess` via Finset.card_bij
- Implemented `maxTrail E v` (noncomputable, terminates by Finset.card_erase_lt_of_mem)
- Proved `maxTrailRem_subset` and `maxTrailRem_last_no_out` by strong induction
- **Proved `maxTrail_closed`**: in a balanced digraph, every greedy maximal trail is a closed circuit
  (balance contradiction: if last ≠ start then outDegree + 1 ≤ outDegree, impossible)
- Proved `circuit_exists`: every non-empty balanced digraph contains a directed circuit
- Added `DirectedCircuit` structure, `remove_circuit_balanced` (1 sorry), `euler_path_implies_degree_balance` (1 sorry)
- Fixed malformed code from context compaction (removed incomplete `?_` placeholders)
- Created PR from `research/konigsberg-hierholzer` branch

### Key Findings

- `maxTrail` terminates via `Finset.card_erase_lt_of_mem` — erase one edge per step
- `maxTrailRem_last_no_out` proved by strong induction using `Nat.strong_rec_on`
- The balance contradiction in `maxTrail_closed` uses:
  1. `maxTrail_last_exhausted`: all outgoing edges of last vertex were used (sorried helper)
  2. `maxTrail_steps_distinct`: each edge used at most once (sorried helper)
  3. `open_walk_last_target_excess`: target-count = source-count + 1 at last vertex
  4. `h_tgt_le_in`: target positions inject into incoming edges
  5. Balance: inDegree = outDegree → contradiction
- `walk_source_eq_outDegree` and `walk_target_eq_inDegree` (from Session 2) are the bijection helpers

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (390 → 867 lines, axioms still 2)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (knowledge updated)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this file created)

### What Remains

Sorried in this session (6 total):
- `maxTrail_used_eq`: E \ maxTrailRem = steps-as-edges set (induction on E.card)
- `maxTrail_last_exhausted`: follows from maxTrailRem_last_no_out + maxTrail_used_eq
- `maxTrail_steps_in_E`: each step uses an edge from E (induction on E.card)
- `maxTrail_steps_distinct`: no edge used twice (induction, edge erased at each step)
- `remove_circuit_balanced`: circuit balance sub-lemma (follows from closed_walk_balance)
- `euler_path_implies_degree_balance`: necessity for paths (needs pigeonhole + open-walk counting)

### Next Steps

1. Prove the 4 `maxTrail` inductive properties — each is ~30 lines of strong induction
2. Once those are done, `maxTrail_closed` + `circuit_exists` + `remove_circuit_balanced` give
   the main ingredients for Hierholzer's theorem (circuit splicing remains)
3. `euler_path_implies_degree_balance`: add `∃!` unique coverage to `HasEulerianPath` definition,
   then apply `open_walk_first_source_excess`/`open_walk_last_target_excess`

---

## Session 2026-05-03 (Session 2) - Implement handshaking lemma proofs

**Mode**: FRESH (continued from Session 1)
**Outcome**: progress — axiomCount 5→2, PR #15170

### What I Did

- Proved `sum_outDegree_eq_edgeCount` and `sum_inDegree_eq_edgeCount` via double-counting
- Added `closed_walk_balance`, `walk_source_eq_outDegree`, `walk_target_eq_inDegree` (bijection lemmas)
- Proved `eulerian_circuit_implies_balanced` (necessity) via walk-position bijection + closed walk rotation
- Updated meta.json: axiomCount 5→2 (was 3 after handshaking, then 2 after necessity)

### Key Findings

- Handshaking via `Finset.sum_comm`: expand |{e: e.1=v}| as ∑_e [e.1=v], swap sums, get ∑_e 1 = |E|
- Necessity: `ExistsUnique` uniqueness + `Finset.card_bij` + closed walk rotation bijection
- `sum_ite_eq` vs `sum_ite_eq'` distinction: condition form determines which variant
