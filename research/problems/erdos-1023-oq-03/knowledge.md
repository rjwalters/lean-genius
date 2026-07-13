# erdos-1023-oq-03 — knowledge

## Status
SOLVED / verified, 0-axiom. File `proofs/Proofs/Erdos1023ProblemOQ03.lean`.
Isolates the axiom-free **lower-bound** half of Erdős #1023 (union-free families
`F(n) = max size with no member the union of ≥2 others`).

## Established (parent + prior sessions)
- `unionFreeMax_ge_choose`: `F(n) ≥ C(n,k)` for every layer `k` (every layer is
  an antichain, antichains are union-free).
- `unionFreeMax_exponential_lower_bound`: `2ⁿ ≤ (n+1)·F(n)`, i.e. `F(n) ≥ 2ⁿ/(n+1)`.
- `unionFreeMax_mono` / `unionFreeMax_le_succ`: `F(n) ≤ F(m)` for `n ≤ m`, via a
  relabelling push-forward `pushFamily e` (preserves card + union-freeness).

## This session (2026-06-24, researcher-1)
Added **strict monotonicity**, sharpening `F(n) ≤ F(n+1)` to `F(n) < F(n+1)`:
- `unionFree_insert_fresh`: adjoining a set `A` containing a ground element `x`
  in no member of `F` keeps `insert A F` union-free. Fresh `x` blocks every
  spurious union (a union = `A` must omit `x`; a union = some `B∈F` cannot use
  `A` without forcing `x∈B`).
- `unionFreeMax_succ_strict`: `F(n) + 1 ≤ F(n+1)`. Extract an extremal family `G`
  via `Nat.sSup_mem` (sSup of a nonempty bounded ℕ-set is attained), push it into
  `Fin (n+1)` along `Fin.castLEEmb (Nat.le_succ n)`, adjoin `{Fin.last n}` —
  fresh because `castLE` values are `< n`.
- `unionFreeMax_strictMono`: `StrictMono unionFreeMax`, via
  `strictMono_nat_of_lt_succ`.

### Gotchas
- Fresh worktree off `origin/main` has NO mathlib build cache → re-clones deps,
  `unknown module prefix 'Mathlib'`. Build in the MAIN checkout (`cp` file in,
  `git checkout --` to restore), `git` from the worktree.
- `Finset.card_insert_of_not_mem` deprecated → `Finset.card_insert_of_notMem`.
- `(Fin.castLE h a : ℕ) = (a : ℕ)` is `rfl`; `(Fin.last n : ℕ) = n` is
  `Fin.val_last` → close freshness with `omega`.
- `Nat.sSup_mem hne bdd` gives membership; ascribe the `obtain` type with
  `unionFreeMax n` (def-eq to the `sSup`) so `hGcard : G.card = unionFreeMax n`.

## Still open
1. Tighten `2ⁿ/(n+1)` toward sharp `C(n,⌊n/2⌋)` (axiom-free Stirling estimates).
2. Axiom-free Erdős–Kleitman upper bound `F(n) ≤ C(n,⌊n/2⌋)` (removes parent's
   Problem-447 axioms).
3. Quantitative growth: axiom-free `F(n+1) ≥ F(n) + g(n)` with `g(n) → ∞`
   (the fresh-element trick only gives `+1`).
4. `k`-union-free / other forbidden Boolean operations.
