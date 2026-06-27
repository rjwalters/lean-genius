# Erdős #340 OQ-05: B_h Sequences

**Open question (generalization) from gallery proof `erdos-340-greedy-sidon`.**

The parent entry develops the theory of Sidon sets (= B_2 sequences: all pairwise
sums distinct) and proves the upper bound `|A| = O(√N)` for `A ⊆ {1,…,N}`. OQ-05
asks whether this extends to **B_h sequences**: sets in which all `h`-fold sums
(with repetition) are distinct.

## Summary

`Erdos340GreedySidonOQ05.lean` formalizes the foundational B_h theory and the sharp
B_h analogue of the Sidon upper bound, fully verified (0 sorries, 0 axioms beyond
`propext`/`Classical.choice`/`Quot.sound`).

| Result | Statement |
|--------|-----------|
| `IsBh h A` | `A` is B_h: the multiset-sum map is injective on `A.sym h` |
| `IsBh.subset` | B_h is inherited by subsets |
| `isBh_one` | every finite set is B_1 |
| `IsBh.of_succ` | downward closure: `B_{h+1}` ⟹ `B_h` |
| `IsBh.of_le` | downward closure (general): `k ≤ h`, `B_h` ⟹ `B_k` |
| `IsBh.sum_injOn_powersetCard` | the `h`-element **subsets** of a B_h set have distinct sums |
| `IsBh.choose_card_le` | **main:** `A ⊆ [1,N]`, B_h, `h ≥ 1` ⟹ `Nat.choose |A| h ≤ h·N` |
| `IsBh.two_card_mul_pred_le` | Sidon recovery: `|A|·(|A|-1) ≤ 4N` (i.e. `|A| = O(√N)`) |

The bound `Nat.choose |A| h ≤ h·N` gives `|A| = O(N^{1/h})`, the trivial B_h
ceiling that Bose–Chowla constructions meet to within `(1-o(1))`.

## Sessions

### Session 2026-06-27 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (verified increment)

#### What I Did
- Defined `IsBh h A` as injectivity of the multiset-sum map `s ↦ (s : Multiset ℕ).sum`
  on the finset `A.sym h` of `h`-element multisets — the clean generalization of the
  parent `IsSidon` (B_2).
- Proved the structural lemmas `IsBh.subset` and `isBh_one`.
- Proved `IsBh.sum_injOn_powersetCard`: the `h`-element subsets of a B_h set have
  pairwise distinct sums (a subset is a repetition-free multiset, so distinctness is
  inherited from the B_h injectivity).
- Proved the **main theorem** `IsBh.choose_card_le`: `Nat.choose |A| h ≤ h·N` for a
  B_h set `A ⊆ {1,…,N}` with `h ≥ 1`, by injecting the `choose(|A|,h)` distinct
  subset-sums into the interval `[1, h·N]`.
- Proved `IsBh.two_card_mul_pred_le`, the explicit `h = 2` specialization, recovering
  the classical Sidon bound.

#### Key Findings
- **Route through `h`-subsets, not all `h`-multisets.** `Finset.sym s n` has no direct
  multichoose cardinality lemma in Mathlib (only the Fintype-level
  `Sym.card_sym_eq_choose`). Using `Finset.powersetCard` (with `Finset.card_powersetCard
  = Nat.choose`) for the counting, while keeping `A.sym h` only for the *definition*,
  makes the bound clean: `card_image_of_injOn` + `Nat.card_Icc` finish it.
- **Evenness needed at `h = 2`.** From `choose(k,2) = k(k-1)/2 ≤ 2N`, deriving
  `k(k-1) ≤ 4N` needs `2 ∣ k(k-1)` (`(Nat.even_mul_pred_self k).two_dvd`); without it
  `omega` finds the spurious counterexample `k(k-1) = 4N+1`.
- **Build infra gotcha.** The host disk was at 100% with ~10 concurrent Docker Lean
  builds thrashing the shared mathlib build dir (disk-I/O / permission-denied errors).
  The worktree's `.lake/packages` is an absolute symlink that breaks inside the
  container. Verified instead by invoking the host `v4.26.0` toolchain `lean` directly
  on the single file with a hand-built `LEAN_PATH` over the existing package oleans —
  no mathlib rebuild, low memory. `#print axioms` confirms 0-axiom.

#### Files Modified
- `proofs/Proofs/Erdos340GreedySidonOQ05.lean` (new, 206 lines, verified)
- `src/data/research/problems/erdos-340-greedy-sidon-oq-05.json` (new)

#### Next Steps
- B_h greedy extension + the `N^{1/(2h-1)}` greedy lower bound — the genuine open
  direction, matching the still-open parent #340.
- Optional exact bridge `IsBh 2 A ↔ Erdos340.IsSidon A`.

### Session 2026-06-27 (Session 2, researcher-10) — downward closure

**Mode**: ACT · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

#### What I Did
- Closed the first listed next-step: the **downward closure** in `h`.
  - `IsBh.of_succ`: `B_{h+1} ⟹ B_h`. Append a fixed `a ∈ A` to two `h`-multisets
    with equal sums; the consed `(h+1)`-multisets land in `A.sym (h+1)` with equal
    sums (each is the common sum plus `a`), so `B_{h+1}` injectivity gives
    `a ::ₛ s = a ::ₛ t`, and `Sym.cons_inj_right` cancels the head. The `A = ∅` case
    is degenerate (`∅.sym 0` is a `Unique` subsingleton; `∅.sym (k+1) = ∅`).
  - `IsBh.of_le`: `k ≤ h ⟹ B_h ⟹ B_k`, iterating `of_succ` via `Nat.le_induction`
    (revert the `B_h` hypothesis so the motive stays type-correct).

#### Key Findings / gotchas
- `hsum : (fun s => (↑s).sum) s = …` arrives as an un-beta-reduced lambda app; bind
  it to an explicitly-typed `have hsum0 : (s:Multiset).sum = (t:Multiset).sum := hsum`
  (defeq) before `rw`, else `rw [hsum]` fails to find the pattern.
- `Finset.not_mem_empty` is deprecated → `Finset.notMem_empty`.
- API used: `Sym.cons` (`::ₛ`), `Sym.coe_cons`, `Multiset.sum_cons`,
  `Sym.cons_inj_right`, `Sym.mem_cons`, `Finset.mem_sym_iff`, `Finset.sym_empty`,
  `Sym.uniqueZero`/`Subsingleton.elim`.

#### Verification
`lake env lean Proofs/Erdos340GreedySidonOQ05.lean` → exit 0, no warnings (Docker
host has a v4.26.0 lean image but per-file `lake env lean` over the symlinked main
`.lake` cache is faster/safer). `#print axioms` on `of_succ`/`of_le` = only the 3
foundational. lineCount 206 → 258, theoremCount 6 → 8.
