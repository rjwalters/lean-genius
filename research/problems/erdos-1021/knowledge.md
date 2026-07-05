# Erdős #1021 — Extremal numbers for the bipartite pair graph G_k

**Status: OPEN.** For every k ≥ 3, is there c_k > 0 with ex(n, G_k) ≪ n^{3/2 − c_k}?
Even ex(n, G_k) = o(n^{3/2}) is unknown for any k ≥ 4. k=3 (G_3 = C_6) solved:
ex(n, C_6) ≪ n^{7/6} (Bondy–Simonovits), so c_3 = 1/3.

## Verified sub-results shipped (gallery entries, all 0-axiom / 0-sorry)

- **erdos-1021-wip-01** (`Erdos1021Wip01.lean`): local degree structure of G_k —
  pair side 2-regular (degree 2), primary side degree k−1, handshake 2·C(k,2)=k(k−1).
- **erdos-1021-oq-01-incomplete-01** (`Erdos1021OQ01Incomplete01.lean`): asymptotic
  boundary — exponent gap gap(k)=1/(k−1)→0, lowerExp→3/2, o⟹O collapse.
- **erdos-1021-wip-02** (`Erdos1021Wip02.lean`, PR #32481, 2026-07-01): **G_k is
  C₄-free** — any two distinct vertices have ≤1 common neighbour (codegree ≤ 1),
  so no K_{2,2}/no 4-cycle. This is exactly the KST/Reiman hypothesis giving the
  trivial ex(n,G_k)=O(n^{3/2}). Key thms: Gk_common_neighbors_subsingleton,
  Gk_codegree_le_one, Gk_no_C4.

## Design notes for future sessions

- The parent `Erdos1021Problem.lean` does NOT reliably compile (Gk_bipartite ↔/→
  precedence bug; cycleGraph loopless). Wip01/Wip02/Incomplete01 all re-declare G_k
  locally (self-contained, import Mathlib only). Keep this pattern.
- G_k vertex type: `Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}`. Pair vertex ⟨(a,b)⟩ ~
  primaries a,b only.
- Proof-tactic recipe (Wip02): use projection-free adjacency iff-lemmas
  (adj_primary_pair : y_i ~ ⟨(a,b)⟩ ↔ i=a∨i=b) so `rcases` on the disjunctions + `omega`
  closes the Fin arithmetic. omega does NOT reduce `(a,b).1` — `dsimp only at` the
  ordering hyps first. omega DOES use `¬(a=c ∧ b=d)` and Fin `i ≠ j`.

## Genuinely hard remaining sorries (deep, not routine)

- `Erdos1021Problem.lean`: `k3_case_solved` (needs Bondy–Simonovits ex(n,C_6)≪n^{7/6}),
  `trivial_bound` (needs a Lean KST theorem — none in Mathlib yet).
- The KST/Reiman O(n^{3/2}) upper-bound counting is the natural next BUILD target now
  that C₄-freeness (its hypothesis) is verified — but it is a substantial (>500 line)
  extremal-counting formalization, not a quick win.

## Next-step suggestions (all still on the OPEN side)

1. BUILD a verified KST/Reiman counting lemma "C₄-free ⇒ e(G) ≤ ½(1+√(4n−3))n" and
   combine with Gk_no_C4 to discharge `trivial_bound`. (Large but self-contained.)
2. k=3 special case: prove G_3 ≅ C_6 from the adjacency description (finite, decidable).
