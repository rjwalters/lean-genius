# Knowledge Base: hurwitz-theorem-oq-03-wip-01

Insights accumulated during research on completing the even-case impossibility of
Hurwitz's theorem (`n`-square identities exist only for `n ∈ {1,2,4,8}`).

---

## Problem Understanding

`HurwitzTheorem.lean` (`hurwitz_only_if`, line ~1904) discharges every case except a
single `sorry` (line ~1937) for the **even, non-admissible** case. The `crossMat`
family `Mⱼ = crossMat nsi j₀ j` (`j ∈ Fin n \ {j₀}`) gives `n-1` matrices with
`Mⱼᵀ = -Mⱼ`, `MⱼᵀMⱼ = I`, `Mⱼ² = -I`, `MⱼMₖ + MₖMⱼ = 0` — a representation of the
Clifford algebra `Cl(0, n-1)` on `ℝⁿ`. The odd case dies by `no_odd_nsquare`
(`det(M)² = (-1)ⁿ = -1`, impossible over `ℝ`). The even case is the classical
Hurwitz–Radon obstruction; the sharp form needs the minimal faithful real
representation dimension of `Cl(0,n-1)` (Bott periodicity + Artin–Wedderburn),
which is **not in Mathlib**.

## The tractable strip: `n ≡ 2 (mod 4)`

The `HurwitzTheoremOQ03WIP01.lean` gallery entry (`HurwitzOQ03WIP01` namespace)
pushes the *elementary* determinant argument one residue class further, into
`n ≡ 2 (mod 4)`, via the field-agnostic engine
`anticommuting_invertible_forces_even` (two anticommuting invertible matrices force
even dimension over any field with `2 ≠ 0`) and its odd-dimension contrapositive
`no_anticommuting_complex_structures_of_odd`.

The plan to close `n ≡ 2 (mod 4)` (only `n ≡ 0 mod 4` then remains blocked):

1. Form `P = M₁ ⋯ M_{n-1}` over the `crossMat` family.
2. `P` commutes with each `Mᵢ`.
3. `P² = -I` for `n ≡ 2 (mod 4)`.
4. View `(ℝⁿ, P)` as a `ℂ`-vector space of complex dimension `m = n/2` (odd when
   `n ≡ 2 mod 4`); `M₁, M₂` become anticommuting `ℂ`-linear complex structures, and
   `no_anticommuting_complex_structures_of_odd` over `ℂ` (with `m` odd) gives the
   contradiction — mirroring the real odd case one level up.

## Progress this session (researcher-2, 2026-07-07) — VERIFIED

Added the **product engine** to `HurwitzTheoremOQ03WIP01.lean` (0 sorry / 0 axiom,
docker-build green, arbitrary ring `R`):

- `mul_prod_anticomm : (∀ x ∈ t, a*x = -(x*a)) → a * t.prod = (-1)^t.length * (t.prod * a)`
  — the move-through sign lemma. Proof: induction on the list; the head anticommutes
  (`hb`), the tail commute of `(-1)^k` past the head factor is `Commute.neg_one_left`
  `|>.pow_left`, closed with `noncomm_ring` (`-1` is central; do **not** use `ring` —
  the ring is noncommutative).
- `commute_prod_of_anticomm_of_even` — even length ⇒ `a` commutes with `t.prod`
  (via `Even.neg_one_pow`).
- `anticommute_prod_of_anticomm_of_odd` — odd length ⇒ `a` anticommutes with `t.prod`
  (via `Odd.neg_one_pow`).

This is the reusable algebraic core behind steps 1–2 of the plan, stated abstractly so
it applies verbatim to the real `crossMat` family and to its complexification. It does
**not** by itself close the case.

## Concrete next steps (worked out; a future session / Aristotle can finish)

- **`P² = -I` (step 3), abstract form.** For a list `L` whose entries pairwise
  anticommute and each square to `-1`, `L.prod * L.prod = (-1)^((L.length+1).choose 2)`.
  Induction on `L = a :: t`, `t.length = j`: using `mul_prod_anticomm` twice,
  `(a*t.prod)² = (-1)^(j+1) · (t.prod)²`, and the exponent recurrence is
  `(j+2).choose 2 = (j+1).choose 1 + (j+1).choose 2 = (j+1) + (j+1).choose 2`
  (`Nat.choose_succ_succ`, `Nat.choose_one_right`) — this avoids all `Nat` division.
  Then for `n ≡ 2 (mod 4)`, `L = [M₁,…,M_{n-1}]`, `(n-1+1).choose 2 = n(n-1)/2`, which is
  **odd** (n = 4k+2 ⇒ n(n-1)/2 = (2k+1)(4k+1), a product of two odds), so `P² = -I`.
- **`P` commutes with each factor `Mᵢ` (step 2).** Not a direct corollary of
  `mul_prod_anticomm` (a factor does not anticommute with itself). Needs a split
  `L.prod = pre * Mᵢ * suf` at index `i` (`List.take/List.drop`), moving `Mᵢ` to its
  own slot and collapsing `Mᵢ² = -1`; the two positional signs `(-1)^{i-1}` and
  `(-1)^{k-i}` combine to `(-1)^{k+1} = +1` for `k = n-1` odd. ~100–200 lines.
- **THE BLOCKER — complexification (step 4).** Turning `(ℝⁿ, P)` with `P² = -I` into a
  `ℂ`-module and reinterpreting the real `M₁, M₂` (which commute with `P`) as `m × m`
  **complex** matrices preserving `det`/anticommutation is the genuine Mathlib gap:
  the equivalence `Mat_n(ℝ)^{commutes with J} ≅ Mat_{n/2}(ℂ)` (for `J² = -I`) is not in
  Mathlib. Without it, the engine (which lives over `ℂ`) cannot be applied to halve the
  dimension to the odd `m = n/2`. This — not steps 1–3 — is what keeps even `n ≡ 2 mod 4`
  from being fully closed by elementary means.
- The residual `n ≡ 0 (mod 4)`, `n ∉ {4,8}` case remains genuinely blocked on Clifford
  representation theory (Bott periodicity + Artin–Wedderburn), as before.

## Dead Ends / Gotchas

- `ring` fails inside these lemmas: `Matrix (Fin m) (Fin m) K` and the abstract `R` are
  **noncommutative**; use `noncomm_ring` and supply centrality of `(-1)^k` explicitly via
  `Commute.neg_one_left … |>.pow_left`.
- Transient `exit 135` (SIGBUS, ~370 ms, no Lean error) is shared-cache corruption, not a
  proof error — retry clears it (observed this session: first run 135, retry surfaced the
  real elaboration error, third run green).

## References

- Hurwitz (1898); Radon (1922). Hurwitz–Radon function.
- `HurwitzTheorem.lean` (`hurwitz_only_if`, `no_odd_nsquare`, `crossMat_*`).
- `HurwitzTheoremOQ03WIP01.lean` (`anticommuting_invertible_forces_even`, product engine).
