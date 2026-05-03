# Problem: Directed Eulerian Theory (konigsberg-oq-01-oq-02)

Extend the Eulerian circuit characterization to directed graphs. A weakly connected digraph has
an Eulerian circuit iff every vertex has equal in-degree and out-degree; directed analogue of
Königsberg bridges.

**Current status**: ACT — 2 of 5 axioms proved (handshaking lemmas); 3 axioms remain.

---

## Session 2026-05-03 (Session 1) - Prove directed handshaking lemmas

**Mode**: FRESH
**Outcome**: progress — axiomCount reduced from 5 to 3

### What I Did

- Identified that `sum_outDegree_eq_edgeCount` and `sum_inDegree_eq_edgeCount` were axiomatized
  but provable via Finset partition
- Proved both using `Finset.card_biUnion`: partition `G.edges` by first/second endpoint,
  show disjointness via `Finset.disjoint_left` and `Finset.mem_filter`, show coverage by `ext`
- Added `directedTriangle_handshaking` as explicit instance verification
- Added `eulerian_balanced_sum_zero` and `eulerian_balanced_implies_degree_balance` as consequences
- Updated meta.json: axiomCount 5→3, theoremCount 5→8, lineCount 193→233

### Key Findings

- `Finset.card_biUnion` is the right tool: disjoint parts covering all edges gives sum of cardinalities = total
- Disjointness for filtered Finsets: `Finset.disjoint_left` + `simp [Finset.mem_filter]` closes quickly
- Coverage proof: `ext e; simp [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter]`; forward is immediate from `e.1 ∈ Finset.univ`
- The 3 remaining axioms require deeper infrastructure:
  - `eulerian_circuit_implies_balanced`: walk bijection over `List.get` positions (~150 lines)
  - `directed_eulerian_iff`: Hierholzer's algorithm (not in Mathlib4)
  - `directed_euler_path_iff`: path version of the above

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (193→233 lines, 5→3 axioms, 5→8 theorems)
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json` (axiomCount, theoremCount, lineCount, sections updated)

### Next Steps

- Prove `eulerian_circuit_implies_balanced`: for closed walk `w` using each edge once, define
  `positions_in(v) = {i | w[i] = v}` and `positions_out(v) = {i | w[i+1] = v}`; show bijection
  via `i → i-1 mod |w|`
- Check KonigsbergOQ02.lean for reusable walk/path infrastructure
- Submit Aristotle job for `eulerian_circuit_implies_balanced` if clean sorry formulation can be written
