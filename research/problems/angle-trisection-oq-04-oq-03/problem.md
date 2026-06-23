# Problem: Pierpont Prime Criterion for Neusis-Constructible n-gons

**Slug**: angle-trisection-oq-04-oq-03
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `AngleTrisectionOQ04.lean` establishes the tool hierarchy
(compass < compass+neusis < compass+origami) and characterizes what is constructible
with each tool. This open question asks:

**Can the Pierpont prime criterion for neusis-constructible regular n-gons be
formalized in Lean 4?**

The Gauss-Wantzel theorem characterizes compass-and-straightedge constructible n-gons
via Fermat primes: a regular n-gon is constructible iff n = 2^k · p₁ · ... · pₘ where
each pᵢ is a Fermat prime (prime of the form 2^(2^j) + 1).

The analog for neusis construction uses **Pierpont primes**: primes of the form
2^u · 3^v + 1. A regular n-gon is neusis-constructible iff n = 2^a · 3^b · p₁ · ... · pₘ
where each pᵢ is a Pierpont prime > 3.

### Formal Statement

```lean
-- A prime p is a Pierpont prime if p - 1 = 2^u * 3^v for some u, v ≥ 0
def IsPierpontPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ u v : ℕ, p - 1 = 2 ^ u * 3 ^ v

-- A number n has the Pierpont factorization form
def HasPierpontForm (n : ℕ) : Prop :=
  ∃ a b : ℕ, ∃ ps : List ℕ,
    (∀ p ∈ ps, IsPierpontPrime p ∧ p > 3) ∧
    n = 2 ^ a * 3 ^ b * ps.prod

theorem pierpont_criterion (n : ℕ) (hn : 3 ≤ n) :
    IsNeusisConstructible (regularPolygon n) ↔ HasPierpontForm n := by
  sorry
```

### Why This Matters

- Direct extension of Gauss-Wantzel theorem (compass → neusis)
- Connects Galois theory (field extensions of degree 2^a · 3^b) to constructibility
- Pierpont primes: 2, 3, 5, 7, 13, 17, 19, 37, 73, 97, 109, 163, 193, 257...
- The neusis-constructible n-gons include all Fermat prime cases plus 7-gon, 9-gon, 13-gon...

## Known Results

### From Parent Proof (`AngleTrisectionOQ04.lean`)

The gallery establishes:
- Tool hierarchy: compass-only ⊂ compass+neusis ⊂ compass+origami
- `trisection_by_neusis`: angle trisection is possible with neusis
- `impossible_with_compass_only`: angle trisection impossible with compass alone
- `neusis_constructs_cube_root`: neusis can extract cube roots
- Framework for neusis-constructible sets

### Mathematical Facts

1. **Pierpont (1895)**: Regular n-gon is constructible by ruler and compass with angle
   trisection (= neusis) iff n = 2^a · 3^b · p₁ · ... · pₘ with pᵢ Pierpont primes > 3
2. **Galois theory**: Neusis corresponds to field extensions of degree dividing 2^a · 3^b
   (not just powers of 2)
3. **Examples**: n=7 (Pierpont prime 7 = 2·3+1), n=9 (=3²), n=13, n=19...
4. **Non-examples**: n=11 (11-1=10=2·5, not 2^u·3^v form), n=23...

### Lean 4 / Mathlib Status
- `Nat.Prime`: primality in Mathlib
- `IsFermatPrime`: possibly in Mathlib — check `Mathlib.NumberTheory.FermatPsp`
- Galois theory: `Mathlib.FieldTheory.Galois` — verify degree calculation
- Constructibility: may need to extend parent proof's framework

## Suggested Approach

### Phase 1: OBSERVE
1. Read `AngleTrisectionOQ04.lean` to understand `IsNeusisConstructible` definition
2. Check what "constructible" means formally in the parent proof
3. Search Mathlib for Fermat prime or Pierpont prime definitions
4. Assess: does the parent proof have enough infrastructure for the criterion?

### Phase 2: ORIENT
1. What does `IsNeusisConstructible` type look like in parent?
2. How does Galois theory connect to constructibility in the parent framework?
3. Is the Gauss-Wantzel theorem itself formalized? (If so, extension is cleaner)

### Phase 3: DECIDE
1. If Gauss-Wantzel is formalized: prove Pierpont as the "≡ mod 2 vs mod 6" analog
2. If not: may need to build field degree characterization from scratch
3. Simplest: prove `IsPierpontPrime` definition and the small cases (n=7, 9)

### Phase 4: ACT

```lean
def IsPierpontPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ u v : ℕ, p - 1 = 2 ^ u * 3 ^ v

-- Verify small Pierpont primes
example : IsPierpontPrime 2 := ⟨Nat.prime_two, 1, 0, by norm_num⟩
example : IsPierpontPrime 3 := ⟨Nat.prime_three, 1, 1, by norm_num⟩
example : IsPierpontPrime 5 := ⟨by norm_num, 2, 0, by norm_num⟩
example : IsPierpontPrime 7 := ⟨by norm_num, 1, 1, by norm_num⟩
example : IsPierpontPrime 13 := ⟨by norm_num, 2, 1, by norm_num⟩
```

## Related Gallery Proofs

- `angle-trisection-oq-04`: Parent — tool hierarchy and neusis constructibility
- `angle-trisection`: Grandparent — compass impossibility
- `gauss-wantzel`: Related — Fermat prime criterion for compass construction

## Quality Assessment

- **Tractability**: 6/10 — well-defined criterion, needs Galois theory infrastructure
- **Significance**: 7/10 — natural extension of Gauss-Wantzel, Pierpont's original result
- **Domain**: Geometry / constructibility / Galois theory / number theory
- **Risk**: Medium — depends on parent proof's constructibility framework
