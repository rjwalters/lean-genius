# S6d ACT (part i) — the icosahedron is NOT 2-flat magic (researcher-3, 2026-07-24)

## Result

New leaf `proofs/Proofs/Erdos735OQ04Icosahedron.lean` (~530 LOC, 0 axioms,
0 sorries): `icosa_not_isKFlatMagic : ¬ IsKFlatMagic 2 icosaConfig`, where
`icosaConfig` is the regular icosahedron at the standard golden-ratio
coordinates (cyclic permutations of `(0, ±1, ±φ)`, `φ = (1+√5)/2`).

With S6a (tetrahedron IS 2-flat magic) and S6b/c (octahedron and cube are
NOT), the score on Platonic solids is: only the tetrahedron — i.e. only the
simplex, consistent with the S6e general-position theorem — is 2-flat magic
among the four solids checked. Remaining: the dodecahedron (S6d part ii).

## The certificate (4 flats, following the S6b/c recipe)

- `flatIY` (y = 0): golden rectangle {r₅,r₆,r₇,r₈} = {(±φ,0,±1)};
- `flatIX` (x = 0): golden rectangle {r₉,…,r₁₂} = {(0,±1,±φ)};
- `flatF1` (x + (φ+1)z = 2φ+1): the face {(φ,0,1),(0,1,φ),(0,−1,φ)};
- `flatF2` (x − (φ+1)z = 2φ+1): the mirror face {(φ,0,−1),(0,1,−φ),(0,−1,−φ)}.

(Y) + (X) − (F1) − (F2) = a₇ + a₈ = 0 against positivity; `linarith`.

The key discovery making this light: the two 4-point golden-rectangle planes
and two 3-point face planes interact exactly like the octahedron's coordinate
vs face planes — no symmetry averaging over the 120-element icosahedral group
needed, despite the S6b PREP's expectation that dodeca/icosa would be heavier.

## Golden-ratio handling (the anticipated blocker, resolved cheaply)

ALL φ arithmetic reduces to three lemmas proved once at the top:
- `phi_sq : φ² = φ + 1` — `linear_combination sqrt5_sq / 4` (one line!);
- `one_lt_phi`, `phi_lt_two` — from `2 < √5 < 3` via
  `nlinarith [Real.sq_sqrt, Real.sqrt_nonneg]`.

Per-vertex decisions then close by pattern:
- rational coordinate ⇒ `norm_num [rᵢ, WithLp.ofLp_toLp, (Matrix.cons_val_two,
  tail_cons, head_cons for index 2)]` — exactly the S6b/c idiom;
- `±φ ≠ 0` ⇒ `simp` + `exact phi_ne_zero`;
- face-plane memberships of `(0,±1,±φ)` points ⇒ `linear_combination phi_sq`
  (the plane identity IS the golden quadratic);
- face-plane non-memberships ⇒ `intro h; (n)linarith [phi_sq, one_lt_phi]` —
  after ring-normalization every excluded vertex gives a linear clash.

## Next steps

- S6d part ii: dodecahedron refutation. 20 vertices `(±1,±1,±1)` +
  cyclic `(0,±1/φ,±φ)` (or scaled `(0,±1,±φ²)`); expect the same shape:
  two big planes (pentagon faces have 5 vertices; the z=0 plane holds 4
  cube-type vertices... choose flats after checking counts) minus two small.
  The per-vertex decision count doubles (~80 decisions) but the φ toolkit
  from this file transfers verbatim (import and reuse `phi`, `phi_sq`, …).
- State-sync note: this memo intentionally does NOT touch state.md — the S7
  gallery PR #43431 (same cycle) already rewrites the state.md header;
  editing it here too would create a self-conflict. Next session: fold both
  into the header (S7 COMPLETE + S6d(i) COMPLETE, remaining S6d(ii) dodeca).
- The gallery entry (once #43431 merges) should gain the icosahedron in
  `additionalFiles` + a mainTheorems entry — small enricher/researcher
  follow-up.
