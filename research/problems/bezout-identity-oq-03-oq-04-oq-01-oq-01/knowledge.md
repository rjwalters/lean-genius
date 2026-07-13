# Knowledge: Iterated CRT over Commutative Rings

## Summary

The two-modulus CRT (`crtRing = b·s·m + a·t·n`) folds over a list of
pairwise-coprime moduli to give iterated CRT existence and uniqueness over any
`CommRing`, with no ring-specific machinery.

## Key lemmas / techniques

- **`isCoprime_list_prod`** — an element coprime to every entry of a list is
  coprime to the list product. Two-case list induction folding
  `IsCoprime.mul_right` (`IsCoprime a b → IsCoprime a c → IsCoprime a (b*c)`)
  and `isCoprime_one_right`. This is the lemma the parent OQ named.
- **`crtRing_list_exists`** — pairwise-coprime moduli (encoded
  `List.Pairwise (fun p q => IsCoprime p.2 q.2)`) give a solvable system.
  Induct on the list; `List.pairwise_cons` yields head-vs-tail coprimalities
  (→ `isCoprime_list_prod` gives head coprime to tail product) and the tail's
  own pairwise structure (→ IH). One `crtRing_exists` combines head residue
  with the tail solution; `List.dvd_prod` propagates tail congruences via
  `q.2 ∣ M ∣ y - x` plus `q.2 ∣ x - q.1` and `dvd_add`.
- **`prod_dvd_of_pairwise_coprime` / `crtRing_list_unique`** — the dual fold of
  `IsCoprime.mul_dvd`; `List.pairwise_map` transports pairwise coprimality from
  pairs to their moduli.
- **`crtRing_three`** — three-modulus specialization; build the `List.Pairwise`
  witness with explicit `.cons`/`.nil` and discharge membership with `fin_cases`.

## Gotchas encountered

- `hx _ (by simp)` leaves metavariables — pass the explicit pair
  `hx (a₁, m₁) (by simp)` so Lean knows which list member.
- For the concrete three-element `List.Pairwise`, a `simp` + `rcases` approach
  is fragile (trailing `∨ False` disjunct from `mem_cons` on `[]`). Explicit
  `Pairwise.cons` constructors + `fin_cases hq` is robust.
- Base case `IsCoprime a (List.prod [])`: `simp only [List.prod_nil]; exact
  isCoprime_one_right` (bare `simpa` triggers the unnecessarySimpa linter).
- Docker build down (containerd I/O); compiled via
  `lake env lean -o .lake/build/lib/lean/Proofs/<name>.olean`.

## Remaining open questions

- Repackage as a ring isomorphism `R/(∏ mᵢ) ≅ ∏ (R/mᵢ)` via
  `Ideal.quotientInfRingEquivPiQuotient`.
- Extract an explicit k-modulus reconstruction formula + complexity bound.
- Relax pairwise coprimality to coprimality of successive partial products.
