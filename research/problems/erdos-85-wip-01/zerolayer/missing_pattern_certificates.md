# Farkas certificates for the 24 dispatch-gap patterns (squad 2723-2724)

Model (all clauses certified graph laws — the v12 map):
- atoms over the pattern's reduced parts `K`:
  - `A(m, {a,b,c})`: equal pairwise lcms, `m` = that lcm; load `m` per leg,
    excess 0
  - `B(m=K e, e→f)`: `K f ∣ K e`; load `2m` on `e`, `m` on `f`; excess 2 on `e`
  - `C(m=K e, e)`: load `3m` on `e`, excess 6 on `e`
  - `D(u=K e, e)`: `3 ≤ K e`, `3 ∤ K e`; load `K e`, excess 2 on `e`
- rows per used comp `e` (reduced units):
  - LOAD: `Σ counts·load_e = 12·K e`
  - EXCESS: `Σ counts·excess_e + s_e = 2·(K e − 1)`, with the used-cell
    slack `s_e = Σ_j a_ej(a_je−1) ∈ [−3, 6]` (a-rows sum to 3, entries ≤ 3)

Certificate check (verified programmatically for all 22, against the TRUE
slack interval `[−3,6]`): for every atom column,
`Σ_e y_e·load_e + z_e·excess_e ≤ 0`; and
`Σ_e ( y_e·12·K_e + z_e·2(K_e−1) − max(−3·z_e, 6·z_e) ) ≥ 1`.
Lean endpoint shape: hypotheses = the two row families over atom counts +
`s_e` bounds; proof = the y/z-weighted linear combination via
omega/linarith.  No decide, no enumeration.

| pattern | y (load weights) | z (excess weights) | slack-worst objective |
|---|---|---|---|
| (7,7,2) | [-7, 4, 20] | [-1, -14, -20] | ≥1 (one-sided) |
| (7,4,3,2) | [2, 6, 7, -12] | [-11, -12, -11, -12] | 10 |
| (7,3,3,3) | [3, 3, -1, -2] | [-11, -8, -2, 0] | 17 |
| (7,3,2,2,2) | [3, 8, -12, 9, -6] | [-11, -12, 0, -12, 0] | 15 |
| (6,6,4) | [1, 1, 4] | [-11, -9, -8] | 4 |
| (6,5,5) | [3, 2, 0] | [-11, -10, -7] | 6 |
| (6,5,3,2) | [4, 4, -4, -4] | [-12, -10, 0, -4] | 2 |
| (6,4,4,2) | [4, -2, 4, -4] | [-12, 0, -12, -4] | 4 |
| (6,4,3,3) | [-2, 6, -3, 4] | [-1, -12, 0, -8] | 3 |
| (6,4,2,2,2) | [2, 3, 0, 0, 0] | [-12, -12, 0, 0, -4] | 4 |
| (5,5,4,2) | [-1, 1, 6, -6] | [0, -3, -12, 0] | 3 |
| (5,5,3,3) | [0, 0, 3, 2] | [0, -1, -12, -12] | 1 |
| (5,4,4,3) | [4, 2, 2, -2] | [-10, -12, -12, 0] | 34 |
| (5,4,3,2,2) | [3, 2, -2, 2, 2] | [-9, -12, 0, -12, -6] | 3 |
| (5,3,3,3,2) | [3, -3, 5, -3, 2] | [-8, 0, -12, 0, -2] | 10 |
| (5,3,2,2,2,2) | [3, 8, 0, 0, -12, 0] | [-8, -12, 0, 0, 0, 0] | 8 |
| (4,4,3,3,2) | [0, 0, 0, 1, 0] | [0, 0, -2, -3, 0] | 1 |
| (4,3,3,3,3) | [6, 0, 0, 0, 0] | [-12, 0, 0, -12, -12] | 12 |
| (4,3,3,2,2,2) | [0, 3, 2, 0, 0, 0] | [0, -12, -12, -2, 0, 0] | 2 |
| (4,2,2,2,2,2,2) | [1, 0, 0, 0, 0, 0, 0] | [-4, 0, 0, 0, 0, 0, 0] | 12 |
| (3,3,3,3,2,2) | [0, 0, 0, 0, 4, 4] | [-10, 0, 0, 0, -12, -12] | 2 |
| (3,3,2,2,2,2,2) | [3, 2, 0, 0, 0, 0, 0] | [-12, -12, 0, 0, 0, 0, -2] | 2 |

Index convention: position i in y/z corresponds to the i-th part of the
pattern as written (descending).

ONE-SIDED FORM (matches da1da24776): since balance forces every used-cell
term `a_ej(a_je−1) ≥ 0` (nonzero entries are mutually nonzero), the slack
satisfies `s_e ≥ 0`, so the one-sided law `Σ atom-excess ≤ 2(K e −1)`
(codex's `degree_sixteen_zeroLayer_used_orphan_atomExcess_sum_le`)
suffices for any certificate with ALL z ≤ 0.  All 22 rows above now have
z ≤ 0 — (7,7,2) was re-solved into one-sided form — so NO lower-bound
companion theorem is needed anywhere; each endpoint consumes exactly the
existing load equality + the da1da excess inequality.

## The two integral holdouts (no linear certificate exists)

- **(6,3,3,2,2)**: v12-era death via child-cover kills; the obstruction is
  integral in the count space.  Candidate routes: small case analysis over
  the B/C count parities, or the six_twelve-style filtered-count argument.
- **(6,2,2,2,2,2)**: ALL-EVEN — direct candidate for the antipodal
  classifier recipe used on the certified 13 (orders 18/6: orphan
  classification via used orders 18∨6, halves land on 9/3 or the load
  route).

Reproduction: scratchpad cert generator (session 7fe40e6a); verification
run `cert_verify_out.txt` shows all 22 columns ≤ 0 and objectives ≥ 1.
