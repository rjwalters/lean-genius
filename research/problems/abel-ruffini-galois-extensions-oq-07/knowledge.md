# Knowledge: Burnside's pᵃqᵇ Theorem (abel-ruffini-galois-extensions-oq-07)

## Status (2026-05-08, Iteration 4)

Phase-2 axiomatization with axiom narrowed: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`,
384 lines, 10 theorems, 1 axiom (narrowed to `2 ≤ a ∨ 2 ≤ b`), 0 sorries.

## Key Results

| Theorem | Statement | Axiom-free? |
|---|---|---|
| `pGroup_isSolvable` | `IsPGroup p G → IsSolvable G` | Yes (Mathlib chain) |
| `burnside_pq_a_zero` | `Nat.card G = p^0 · q^b → IsSolvable G` | Yes |
| `burnside_pq_b_zero` | `Nat.card G = p^a · q^0 → IsSolvable G` | Yes |
| `burnside_pq_same_prime` | `Nat.card G = p^a · p^b → IsSolvable G` | Yes |
| `squarefreeOrder_isSolvable` (S4) | `Squarefree (Nat.card G) → IsSolvable G` | Yes (IsZGroup chain) |
| `burnside_pq_pq_case` (S4) | `p ≠ q ∧ Nat.card G = p · q → IsSolvable G` | Yes |
| `burnside_pq_nontrivial` (axiom, narrowed S4) | `p ≠ q ∧ a, b ≥ 1 ∧ (2 ≤ a ∨ 2 ≤ b) ∧ Nat.card G = p^a · q^b → IsSolvable G` | **No (narrowed axiom)** |
| `burnside_pq` | `Nat.card G = p^a · q^b → IsSolvable G` | Uses axiom only for `2 ≤ a ∨ 2 ≤ b` |
| `alternatingGroupFin5_card` (S3) | `Nat.card A₅ = 2^2 · 3 · 5` | Yes |
| `alternatingGroupFin5_not_solvable` (S3) | `¬ IsSolvable A₅` | Yes |
| `burnside_pq_sharp` (S3) | conjunction of above two | Yes |

## Mathlib API anchors

### Core (S2)
- `IsPGroup.iff_card.mpr ⟨n, hcard⟩` : derive `IsPGroup p G` from `Nat.card G = p^n`.
- `IsPGroup.isNilpotent : IsPGroup p G → IsNilpotent G` (in `Mathlib.GroupTheory.Nilpotent`).
- `IsNilpotent G → IsSolvable G` : Mathlib instance, derived via `infer_instance`.
- `Nat.eq_zero_or_pos a : a = 0 ∨ 0 < a` for trivial-case dispatch.
- `eq_or_ne p q : p = q ∨ p ≠ q` for prime-equality split.

### Squarefree route (S4)
- `IsZGroup.of_squarefree : Squarefree (Nat.card G) → IsZGroup G` (in `Mathlib.GroupTheory.SpecificGroups.ZGroup`).
- `instance [Finite G] [IsZGroup G] : IsSolvable G` (same file).
- `Nat.coprime_primes hp hq : Coprime p q ↔ p ≠ q` (in `Mathlib.Data.Nat.Prime.Basic`).
- `Prime.squarefree : Prime x → Squarefree x` (in `Mathlib.Algebra.Squarefree.Basic`).
  Apply via `hp.out.prime.squarefree` (where `hp : Fact p.Prime`).
- `Nat.squarefree_mul (hmn : m.Coprime n) : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n`
  (in `Mathlib.Data.Nat.Squarefree`).

## Why three trivial cases plus pq case collapse

All four trivial cases (`a = 0`, `b = 0`, `p = q`, `|G| = 1`) reduce to G being a
p-group for some prime p:

- `a = 0` → `|G| = q^b` → `IsPGroup q G`.
- `b = 0` → `|G| = p^a` → `IsPGroup p G`.
- `p = q` → `|G| = p^(a+b)` → `IsPGroup p G`.
- `|G| = 1` → degenerate; absorbed by either of the above (since `p^0 = q^0 = 1`).

Mathlib's `IsPGroup → IsNilpotent → IsSolvable` chain then closes them axiom-free.

The squarefree case (`a = b = 1`, `p ≠ q`) reduces to the squarefree route:

- `Nat.card G = p · q` with `p ≠ q` → `Squarefree (p · q)` → `IsZGroup G` → `IsSolvable G`.

This eliminates the `a = b = 1` sub-case of the original `burnside_pq_nontrivial` axiom.
The genuinely-open Lean content is now exactly: `|G|` divisible by `p²` or `q²`
for distinct primes (`2 ≤ a ∨ 2 ≤ b`).

## Two proof routes for `burnside_pq_nontrivial` (residual case, `2 ≤ a ∨ 2 ≤ b`)

### Route A: Burnside 1904 (character theory)
- Pick minimal counterexample G; show G is non-abelian simple with no normal Sylow.
- Pick `g ∈ Z(P)` of prime order (P a Sylow p-subgroup).
- Conjugacy class size `|cl(g)| = |G : C_G(g)|` is divisible only by powers of q.
- Apply column orthogonality of irreducible characters: `Σ χ(1)·χ(g) = 0`.
- Algebraic-integer arithmetic in the cyclotomic ring `ℤ[ζ_n]` derives a contradiction.

**Mathlib gap**: The algebraic-integer hypothesis `(|G|/χ(1))χ(g) ∈ ℤ̄_K` is not
formalized at the needed generality. Estimated 100-200 additional lines on top
of `Mathlib.RepresentationTheory.Character.char_orthonormal`.

### Route B: Goldschmidt-Matsuyama 1970s (character-free)
- Use the focal subgroup theorem: `P ∩ G' = focal subgroup of P in G`.
- Apply transfer homomorphism on Sylow p-subgroup.
- Show `P ∩ G' < P`, contradicting `G = G'` for non-abelian simple G.

**Mathlib status**: `Mathlib.GroupTheory.Focal` provides the focal subgroup
definition, `transferFocal`, `commutator_inf_eq_focalSubgroup`, etc. Significant
scaffolding exists for this route. Estimated 200-400 lines on top of this.

**Recommendation**: Route B (character-free), since Mathlib's `Focal` infrastructure
is closer to ready than the algebraic-integer infrastructure for Route A.

### Sub-case strategy (intermediate Sylow analysis)

Before tackling the full Goldschmidt-Matsuyama proof, the residual axiom can be
narrowed further by proving specific sub-cases via Sylow analysis:

- `|G| = p² · q` (a=2, b=1): ~50-100 lines. Sylow's third theorem gives
  `n_p | q` and `n_q | p²`; case analysis on (n_p, n_q) yields a normal Sylow.
- `|G| = p · q²` (a=1, b=2): symmetric to above.
- `|G| = p² · q²` (a=b=2): more delicate; Sylow + counting elements.

Each of these subsumes a specific instance of the axiom. After all three are
proved, the axiom narrows to `3 ≤ a ∨ 3 ≤ b`.

## Sharpness check

`|A₅| = 60 = 2² · 3 · 5` has THREE distinct primes — exactly one more than
Burnside permits. Combined with the parent gallery entry's
`¬ IsSolvable (Equiv.Perm (Fin 5))`, this gives the exact prime-multiplicity
threshold for solvability: groups of order divisible by ≤ 2 primes are always
solvable; groups divisible by ≥ 3 primes can fail (and A₅ is the smallest).

Note: A₅ also defeats the squarefree route — `|A₅| = 60 = 2² · 3 · 5` has `2²`,
so `squarefreeOrder_isSolvable` does not apply. The squarefree route is strictly
weaker than the full Burnside theorem: it covers any number of distinct primes
each to first power, but cannot handle `p²` for any prime.

## Path forward

1. **(S5)** Prove `|G| = p² · q` axiom-free via Sylow analysis (~50-100 lines).
2. **(S6)** Prove `|G| = p · q²` axiom-free (symmetric, ~30-50 lines).
3. **(S7)** Prove `|G| = p² · q²` axiom-free (~80-150 lines).
4. **(S8+)** Build Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`
   (~200-400 lines). Closes ALL remaining cases.
5. **(Final)** Replace `axiom burnside_pq_nontrivial` with theorem; sync meta.json;
   submit Mathlib upstream PR (~1000 lines total).
