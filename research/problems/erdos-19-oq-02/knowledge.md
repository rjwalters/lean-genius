# Knowledge Base: erdos-19-oq-02

Extensions to k-wise intersections (large-intersection companion to Erdős–Faber–Lovász).

---

## Problem Understanding

Seeker-minted, originally a vague stub ("formal statement to be added"). Parent
`erdos-19` is the Erdős–Faber–Lovász conjecture, which is about set families with
SMALL pairwise intersections (linear hypergraphs, |Aᵢ ∩ Aⱼ| ≤ 1) and is heavily
axiomatized in the gallery. Rather than pile theorems on those axioms, this entry
develops the natural COMPANION theme — families with LARGE (nonempty)
intersections, i.e. **intersecting families** — generalized to **k-wise**
intersection. This is the most defensible reading of "k-wise intersections".

## Resolution (Session 1, 2026-06-25) — COMPLETE, fully verified

`proofs/Proofs/Erdos19OQ02Problem.lean`, 156 lines, 9 theorems + 2 defs, 0 sorries.
`#print axioms` on all main results → only `[propext, Classical.choice, Quot.sound]`
(no sorryAx, no Lean.ofReduceBool). Status verified, badge original.

### Definition
`KWiseIntersecting k 𝒜` (𝒜 : Finset α, α a BooleanAlgebra): every `t ⊆ 𝒜` with
`0 < #t ≤ k` has `t.inf id ≠ ⊥`.

### Results
- `KWiseIntersecting.subfamily`, `.antitone` (j ≤ k ⟹ KWise k → KWise j): direct.
- `KWiseIntersecting.mem_ne_bot` (k ≥ 1): members are ≠ ⊥ (singleton subfamily).
- `KWiseIntersecting.intersecting` (k ≥ 2): the reduction to Mathlib's pairwise
  `Set.Intersecting` — THE bridge. Apply hypothesis to `{a,b}`; its meet is `a ⊓ b`,
  so `a ⊓ b ≠ ⊥` ⟺ `¬ Disjoint a b`.
- `KWiseIntersecting.card_le` (Fintype): `2 * #𝒜 ≤ Fintype.card α` via
  `Set.Intersecting.card_le`.
- `kWiseIntersecting_subsets_card_le`: classical `2 * #𝒜 ≤ 2 ^ n` for subsets of
  `Fin n` (via `Fintype.card_finset`).
- Sharpness: `principalUp a = {x | a ≤ x}`; `principalUp_kWiseIntersecting`
  (a ≠ ⊥ ⟹ KWise k for ALL k), `principalUp_intersecting`,
  `exists_kWiseIntersecting` (nontrivial α ⟹ nonempty example exists).

## Key Lean facts used
- `Set.Intersecting`, `Set.Intersecting.card_le` (Mathlib.Combinatorics.SetFamily.Intersecting).
- `Finset.inf_insert` / `Finset.inf_singleton`: `{a,b}.inf id = a ⊓ b` (need `simp`
  to discharge the residual `id a ⊓ id b = a ⊓ b`).
- `Finset.le_inf` for the principal-up-set lower bound.
- `Fintype.card_finset : |Finset α| = 2 ^ |α|`.
- `disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥`; `le_bot_iff`.

## Gotchas / Lessons
- Finset literals `{a,b}` need `[DecidableEq α]`; `{a}` singleton does NOT. Added
  `[DecidableEq α]` only to `intersecting`, `card_le`, `principalUp_intersecting`.
- `principalUp` filter needs `[DecidableLE α]` (DecidablePred (a ≤ ·)), `[Fintype α]`
  for `univ`; does NOT need DecidableEq (drop it to avoid unused-section-var linter).
- ENV: Docker down + disk 99% full + shared `~/.cache/mathlib` corruption from
  concurrent agents. `cache unpack`/`get` flaked (curl.cfg missing, corrupt ltars).
  WORKAROUND: narrowed `import Mathlib` → the 3 specific modules needed, which only
  loads valid oleans, then `proofs/bin/lake env lean File.lean` (EXIT 0). Build the
  olean with `lake env lean -o <olean> File.lean` before `#print axioms` from a
  second file.

## Follow-ups (recorded in meta openQuestions)
- Prove principal up-set ATTAINS the half bound (2|𝒜| = 2ⁿ for all sets through a point).
- Frankl's structure theorem separating k ≥ 3 from pairwise.
- k-wise t-intersecting refinement.
