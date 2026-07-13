# pell-equation-oq-04-oq-01: Finiteness classification of x² − Dy² = N

**Status**: COMPLETED (0-axiom verified, no native_decide)
**Lean file**: `proofs/Proofs/PellEquationOQ04OQ01.lean` (276 lines, 14 theorems, 3 defs)
**PR**: (this session)

## Problem

Child of `pell-equation-oq-04` (the general norm form x²−Dy²=N: Brahmagupta
multiplicativity, the Pell group, infinitude from a positive seed). The parent left
the *classification* of solution sets open. This entry settles the **finiteness**
half completely.

## Result

For a **positive non-square D**, the solution set `S_N = {(x,y) : x²−Dy²=N}` is
exactly one of:

* **empty** (no representation),
* **the single point `{(0,0)}`** — precisely when `N = 0`,
* **infinite**.

Headline theorems:
- `solution_set_trichotomy` — the three-way classification above.
- `infinite_iff` — `S_N` infinite ⟺ `N ≠ 0 ∧ S_N` nonempty.
- `nonempty_finite_iff_zero` — a nonempty `S_N` is finite ⟺ `N = 0`.
- `solutions_zero` — anisotropy: `x²−Dy²=0` ⟹ `(0,0)` (non-square D).

## Proof architecture

Two Mathlib engines (both needing non-squareness):
1. `Pell.exists_of_not_isSquare` → `exists_unit`: a normalized fundamental unit
   (u ≥ 2, v ≥ 1, u²−Dv²=1). The bound u ≥ 2 comes from u² = 1 + Dv² ≥ 2.
2. `Zsqrtd.norm_eq_zero` → `solutions_zero`: the ℤ[√D]-norm is anisotropic, so
   `normForm D x y = 0` ⟹ x = y = 0. (Identify `normForm D x y` with the norm of
   `⟨x,y⟩ : Zsqrtd D` via `show x*x − D*y*y = 0` + `linear_combination`.)

Bridge: `exists_pos_seed` normalizes ANY nonzero-N solution to a positive seed of
the same norm — `(|x|,|y|)` when x≠0, else compose `(0,|y|)` once with the unit
(`(D|y|v, |y|u)`, norm N·1=N by `linear_combination (-D*|y|^2)*huv + hxy + (-D)*sq_abs y`).
Then the parent-style orbit (re-derived locally) injects ℕ into `S_N`.

## Gotchas / techniques

- `¬ IsSquare (2:ℤ)` is NOT `by decide` (IsSquare = ∃ r, n = r*r, not decidable by
  enumeration). Use `Int.prime_two.not_isSquare` (`Prime.not_isSquare` in
  `Mathlib.Algebra.Prime.Lemmas`).
- `Zsqrtd.norm_eq_zero` hypothesis is `∀ n, d ≠ n*n` (NOT `¬IsSquare`); convert via
  `fun n hn => hsq ⟨n, hn⟩` (IsSquare unfolds to `∃ r, d = r*r`).
- `Zsqrtd.norm ⟨x,y⟩` is defeq `x*x − D*y*y`; prove the value with `show x*x − D*y*y = 0`
  then `linear_combination h` (ring won't unfold the `normForm` def — `simp only [normForm]`
  the hypothesis first).
- `gcongr` discharges `1*1*1 ≤ D*|y|*v` from `1≤D, 1≤|y|, 1≤v` in context by itself
  (a trailing `<;> assumption` is then an unreachable-tactic warning — drop it).
- `Int.one_le_abs (h : z ≠ 0) : 1 ≤ |z|`; `sq_abs : |a|^2 = a^2`.
- 2 ≤ |x| from x²≥2: get x≠0 (`norm_num at hx2` after `rintro rfl`), |x|≥1, and
  |x|≠1 (else x²=1), then `omega` (treats |x|, x^2 as atoms).
- Docker was down → built single-file via `lake env lean` (pinned 4.26.0), produced
  the olean with `-o .lake/build/lib/lean/Proofs/...olean` to run `#print axioms`.
- MAIN-PATH WRITE TRAP again: first Write landed in the main repo (cwd resets to
  worktree but absolute paths to main repo write there); copied into worktree and
  removed the stray. Keep all writes under the worktree path.

## Axioms

All headline theorems: `[propext, Classical.choice, Quot.sound]` only — 0-axiom
verified, no `sorryAx`, no `Lean.ofReduceBool`.

## Follow-up open questions (left for future work)

- Count the Pell-group orbit classes of a solvable N (class-number / genus theory).
- Effective solvability criterion + smallest-solution bound in terms of D, N.
