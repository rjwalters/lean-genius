# erdos-659-oq-01-oq-02 — S1b OBSERVE: Cartesian-lattice falsification at d = 3

**Date**: 2026-05-12
**Author**: researcher-1
**Scope**: doc-only follow-up to S1 OBSERVE (PR #18322 by researcher-10,
merged 2026-05-12 23:19 UTC). Falsifies the proposed upper-bound
construction by exhibiting a **concrete 4-point square** in the
cube-lattice `{(a, b√2, c√3) : a, b, c ∈ [-k, k]}` for `k ≥ 1`,
demonstrating that the `cartesianLattice_fourPointProperty` axiom
(`problem.md:166-167`) is **false as stated** and the S2 ACT
construction needs a prime-pair fix.

**No Lean source changes.** **No** `meta.json`, `problem.md`,
`state.md`, `knowledge.md`, or gallery JSON edits. Adds exactly one
file: this session note.

## 1. The failed axiom

`problem.md` § "S3 — Cartesian-lattice construction (upper bound,
axiomatised)" proposes:

```lean
axiom cartesianLattice_fourPointProperty {d k : ℕ} (hd : d ≥ 3)
    (hk : k ≥ 1) :
    fourPointPropertyD (cartesianLattice d k)
```

with `cartesianLattice d k :=` the set
`{(a₁, a₂√2, a₃√3, …, a_d√p_{d-1}) : a_i ∈ [-k, k]}`,
`p_i` the `i`-th prime. For `d = 3, k ≥ 1` this is

```
L₃ := {(a, b√2, c√3) ∈ ℝ³ : a, b, c ∈ ℤ ∩ [-k, k]}.
```

**Claim (this S1b).** For every `k ≥ 1`, `L₃` contains a 4-point
subset realising only **2** distinct pairwise distances — violating
`fourPointPropertyD` (which requires ≥ 3 distinct distances on every
4-subset).

## 2. The 4-point square at `k = 1`

Take the four points

```
p₁ := (  0,         0,        0  )
p₂ := ( -1,       -√2,        0  )
p₃ := (  0,         0,       -√3 )
p₄ := ( -1,       -√2,       -√3 )
```

All four are in `L₃` for `k ≥ 1` (each coordinate is `0`, `±1`,
`±√2`, or `±√3` from the `{-1, 0, 1}` cube).

### Pairwise squared distances (6 pairs)

| pair        | difference                                      | squared distance       |
|-------------|-------------------------------------------------|------------------------|
| `p₁ – p₂`   | `(1, √2, 0)`                                    | `1 + 2 + 0 = 3`        |
| `p₁ – p₃`   | `(0, 0, √3)`                                    | `0 + 0 + 3 = 3`        |
| `p₂ – p₄`   | `(0, 0, √3)`                                    | `0 + 0 + 3 = 3`        |
| `p₃ – p₄`   | `(1, √2, 0)`                                    | `1 + 2 + 0 = 3`        |
| `p₁ – p₄`   | `(1, √2, √3)`                                   | `1 + 2 + 3 = 6`        |
| `p₂ – p₃`   | `(-1, -√2, √3)` ↦ squared coords `(1, 2, 3)`    | `1 + 2 + 3 = 6`        |

Distinct values: `{3, 6}` — only **2**. The 4-point property requires
≥ 3. ☒

(Numerical cross-check via `python3 -c "import math; …"` confirms
all six squared distances are exactly 3.0 or 6.0 to floating-point
precision.)

### Geometric interpretation

The set `{p₁, p₂, p₃, p₄}` is a *geometric* square: 4 sides of length
`√3` and 2 diagonals of length `√6 = √3 · √2`. Sides are the
"opposite pair" edges of a 2D-embedded square in the 3D ambient.

## 3. Why the failure is intrinsic to `(1, √2, √3)`

Squares in `L₃` correspond to non-zero integer vectors `v, w ∈ ℤ³`
satisfying

```
a² + 2b² + 3c²  =  a'² + 2b'² + 3c'²       (equal squared norms)
aa' + 2bb' + 3cc'  =  0                      (perpendicular in the weighted metric)
```

The S1b counterexample uses `v = (-1, -1, 0)`, `w = (0, 0, -1)`:

- `||v||² = 1 + 2 + 0 = 3`, `||w||² = 0 + 0 + 3 = 3`. Equal because
  `1 + 2 = 3` — i.e., `p_1 + p_2 = p_3` for primes `(p_1, p_2, p_3) =
  (1, 2, 3)` ("1" treated as the trivial axis multiplier).
- `v · w = 0` because `v` has zero third coord and `w` has zero
  first/second coord.

The **load-bearing arithmetic coincidence** is `1 + 2 = 3`. Any
prime-pair `(p, q)` with `1 + p = q` (i.e., `q = p + 1`) produces
the same failure pattern (since `q` prime forces `p = 2`, the only
prime adjacent to another prime). The S1 OBSERVE's specific choice
of "first `d - 1` primes" hits this trap immediately at `d = 3`.

### Same failure persists at larger `k`

A second, independent square at `k = 2`:

```
q₁ = (  0, 0,       0  ),    q₂ = (  1, √2, √3 ),
q₃ = ( -2, √2,      0  ),    q₄ = ( -1, 2√2, √3 ).
```

Here `v = (1, 1, 1)`, `w = (-2, 1, 0)`. Then `||v||² = 6 = 4 + 2 =
||w||²` and `v · w = -2 + 2 + 0 = 0`. All four squared distances at
edges are 6, diagonals 12. Two distinct values, 4-point property
violated.

This shows the failure is **not** a `k = 1` artefact; the lattice
admits infinitely many such 4-subsets as `k → ∞`.

## 4. Computational search: alternative prime pairs

A brute-force Python search (`a, b, c, a', b', c' ∈ [-R, R]`) for
non-parallel perpendicular equal-norm vector pairs in lattices
`{(a, b√p, c√q) : ℤ³}`:

| `(p, q)`  | `R = 3`            | `R = 5`            | smallest `k` admitting a square |
|-----------|--------------------|--------------------|---------------------------------|
| `(2, 3)`  | found `‖·‖² = 3`   | many               | **`k = 1`** (S1b's example)     |
| `(2, 5)`  | none               | none               | `k > 5` (search limit; possibly never) |
| `(2, 7)`  | `‖·‖² = 8`, `k=2`  | many               | `k = 2`                         |

**Empirical takeaway**: `(p, q) = (2, 5)` is the **smallest
prime-pair** for which the construction has the 4-point property up
to `k = 5`. The 2 + 3 = 5 arithmetic coincidence at `(p, q) = (2, 7)`
re-triggers small squares (`||v||² = 8 = 4 + 4 = 1 + 7`).

A complete "prime-pair safety" analysis would need a Diophantine
condition like

```
∀ small a, b, c, a', b', c': (a² + p b² + q c² = a'² + p b'² + q c'²)
                              ∧  (aa' + p bb' + q cc' = 0) ⇒ (a,b,c) ∥ (a',b',c')
```

which is a Pell-equation-style problem in three variables. The
parent slug (`erdos-659-oq-01`) at `d = 2` doesn't hit this because
the 2D lattice `{(a, b√2)}` has no integer solutions to `a² + 2b² =
a'² + 2b'²` with `aa' + 2bb' = 0` and `(a,b) ⊥ (a',b')` (verified
for small ranges; the obstruction is the fundamental Pell equation
`x² - 2y² = ±1`).

## 5. Implications for S2 ACT

### 5.1 The axiom as stated (`problem.md:166-167`) is false

`cartesianLattice_fourPointProperty {d=3, k=1} : fourPointPropertyD
(cartesianLattice 3 1)` is **provably false** in Lean: the 4-point
subset `{p₁, p₂, p₃, p₄}` from § 2 is a counterexample. Axiomatising
it as stated would introduce an inconsistency.

### 5.2 Three fix options

**Option A (recommended): change the axis scaling**. Replace the
"first `d - 1` primes" with a choice that avoids small Diophantine
coincidences. Concretely, for `d = 3`, use `(p, q) = (2, 5)` instead
of `(2, 3)`:

```lean
def cartesianLattice₃ (k : ℕ) : Finset (EuclideanSpace ℝ (Fin 3)) :=
  -- {(a, b√2, c√5) : a, b, c ∈ [-k, k]}
  ...
```

The empirical search through `R = 5` finds no squares; a rigorous
proof requires showing the Pell-equation system has no small
solutions, which is a non-trivial number-theoretic argument
(possibly via the class group of ℚ(√10) or related). For `d ≥ 4`,
one must check the prime-pair safety for every pair
`(p_i, p_j)`; the parent's "consecutive primes" heuristic is
insufficient.

**Option B: restrict `k`**. Take `(p, q) = (2, 3)` but constrain
`k ∈ [1, k_max]` where `k_max` is the largest `k` for which the
lattice still has the 4-point property. § 2 shows `k_max < 1`,
i.e., **the construction fails at every `k`**. So Option B is
ruled out for `(p, q) = (2, 3)`.

**Option C: weaken the construction**. Use *non-cubic* point sets:
e.g., the centroid lattice `{(a, b√2, c√3) : a + b + c ≡ 0 (mod 2)}`
or a sub-lattice that excludes the diagonal axis-aligned squares.
This changes the cardinality from `(2k+1)^d` to roughly half that,
which still gives `n^{2/d}` asymptotics but breaks the closed-form
upper bound `(2k+1)^d`.

### 5.3 Where S1 OBSERVE was right, and where S1b refines it

| Topic                                  | S1 verdict                                     | S1b refinement |
|----------------------------------------|------------------------------------------------|----------------|
| Solymosi–Vu lower bound (S4 axiom)     | axiomatise verbatim                            | ✓ unchanged    |
| `O(k²) = O(n^{2/d})` distinct-distance count from squared-form values | sound          | ✓ unchanged (the bound is on **distinct distances**, not on 4-point property) |
| `cartesianLattice` has 4-point property | claimed axiom (S3)                            | **falsified for `(p, q) = (2, 3)`; needs prime-pair fix** |
| Provisional answer `Θ(n^{2/d})` for `d ≥ 3` | sound                                       | ✓ unchanged (refinement only affects WHICH lattice realises the upper bound, not WHAT the rate is) |
| Risk note 4 ("Cartesian-lattice 4-point property is non-trivial to verify") | flagged | **upgraded from "non-trivial" to "false-as-stated"; needs an actual fix** |

### 5.4 Cost impact

S2 ACT plan was 60 min for `cartesianLattice + 2 axioms + dim_d_upper_bound`. With the fix:
- ≈ 15 min: change axis scaling from `√p_i` to a verified-safe prime-pair (Option A); update construction.
- ≈ 30 min: state the corrected axiom with the *new* prime pair, possibly add a small `decide`-able lemma confirming the 4-point property at `k ≤ 5` by brute-force enumeration (so the axiom is at least **empirically tested** even if not fully proven).
- ≈ 15 min: update `meta.json`, `state.md` "open files" to reflect the fix.

Total revised S2 ACT effort: ~60 min (unchanged), but the axiomatic
content is *different* — the construction's prime choice is now a
load-bearing design decision, not an "anything-goes" detail.

## 6. Sister-slug compatibility

- `erdos-659` (grandparent): 2D Moree–Osburn lattice
  `{(a, b√2) : a, b ∈ [-k, k]}` — 2D Pell equation prevents small
  squares, so the parent's bound is unaffected. ✓
- `erdos-659-oq-01` (direct parent): 2D `O(n/√log n)` bound is
  unaffected. ✓
- `erdos-659-oq-01-oq-01` (sibling, Landau constant): orthogonal to
  S1b. ✓
- `erdos-659-oq-01-oq-03` (sibling, 5-point property): the 5-point
  property is *stronger* than the 4-point property (5-subsets
  determine ≥ 3 distances ⇒ 4-subsets determine ≥ 3 distances). So
  the same `L₃` square at `k = 1` falsifies the 5-point property
  too. A separate S1 OBSERVE on oq-03 should propagate this
  finding.

## 7. Race awareness

At push time:

- `gh pr list --search "erdos-659-oq-01-oq-02" --state open`: **0** open
  PRs on this slug.
- `gh pr list --search "erdos-659" --state open`: **0** open PRs on
  the slug family.
- `git branch -r | grep erdos-659-oq-01-oq-02`: only the merged S1
  OBSERVE branch (`research/erdos-659-oq-01-oq-02-...-1778629615`).
- No `falsification`, `cartesian-lattice-square`, `4-point-counterexample`
  branch on this slug.

S1b is the first follow-up to S1 OBSERVE on this slug. No file
conflict; distinct topic from any in-flight PR.

## 8. Test plan

- [x] 4-point square at `k = 1` verified by direct arithmetic on
  all 6 pair distances (§ 2 table).
- [x] Numerical cross-check via Python: all 6 squared distances
  match exactly (no floating-point drift, since values are exact
  integers `3` and `6`).
- [x] Second independent square at `k = 2` (§ 3) verified by
  arithmetic.
- [x] Alternative prime-pair search (`(2, 5)`, `(2, 7)`)
  completed via brute force `R ≤ 5` (§ 4); `(2, 5)` immune up to
  search limit.
- [x] 2D parent lattice `{(a, b√2)}` cross-check: Pell-equation
  argument confirms no small squares (no integer solutions to
  `a² + 2b² = a'² + 2b'²` with `aa' + 2bb' = 0`).
- [x] Doc-only PR — no Lean build needed.
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` /
  `meta.json` / Lean / gallery JSON.

## 9. Anti-targets

- **No** modification of S1 OBSERVE deliverables (`problem.md`,
  `knowledge.md`, `state.md`, sessions if any) — S1b is purely
  additive.
- **No** Lean changes; S1b is a paper-and-pencil + brute-force
  computational finding.
- **No** claim of "verified" or "axiomatized" status — the slug is
  still pre-S2, no gallery integration.
- **No** speculation about the lower-bound side (Solymosi–Vu is
  separately axiomatic in S4); S1b is **exclusively** about the
  upper-bound construction.
- **No** weakening of the provisional `Θ(n^{2/d})` answer — only
  WHICH lattice realises the upper bound changes; the rate is
  unaffected.
