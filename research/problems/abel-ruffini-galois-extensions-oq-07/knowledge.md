# Knowledge: Burnside's pᵃqᵇ Theorem (abel-ruffini-galois-extensions-oq-07)

## Status (2026-05-08, Iteration 7)

Phase-2 axiomatization with axiom narrowed and one residual instance now
proved axiom-free: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`,
631 lines, 16 theorems/lemmas, 1 axiom (still narrowed to `2 ≤ a ∨ 2 ≤ b`,
but with the `(a, b) = (2, 1) ∧ q < p` instance now axiom-free), 0 sorries.

## Key Results

| Theorem | Statement | Axiom-free? |
|---|---|---|
| `pGroup_isSolvable` | `IsPGroup p G → IsSolvable G` | Yes (Mathlib chain) |
| `burnside_pq_a_zero` | `Nat.card G = p^0 · q^b → IsSolvable G` | Yes |
| `burnside_pq_b_zero` | `Nat.card G = p^a · q^0 → IsSolvable G` | Yes |
| `burnside_pq_same_prime` | `Nat.card G = p^a · p^b → IsSolvable G` | Yes |
| `squarefreeOrder_isSolvable` (S4) | `Squarefree (Nat.card G) → IsSolvable G` | Yes (IsZGroup chain) |
| `burnside_pq_pq_case` (S4) | `p ≠ q ∧ Nat.card G = p · q → IsSolvable G` | Yes |
| `isSolvable_of_normal_quotient_solvable` (S5) | `[N.Normal] [IsSolvable N] [IsSolvable (G ⧸ N)] → IsSolvable G` | Yes |
| `burnside_pq_with_normal_pSylow` (S5) | `Nat.card G = pᵃ · qᵇ ∧ ∃ N normal of order pᵃ → IsSolvable G` | Yes |
| `burnside_pq_with_normal_qSylow` (S5) | `Nat.card G = pᵃ · qᵇ ∧ ∃ N normal of order qᵇ → IsSolvable G` | Yes |
| `sylow_count_eq_one_of_lt_prime` (S7, private) | `n ∣ q prime ∧ q < p ∧ n ≡ 1 [MOD p] → n = 1` | Yes (arithmetic) |
| `factorization_p_sq_q_at_p` (S7, private) | `(p² · q).factorization p = 2` for distinct primes (q < p) | Yes |
| `burnside_p_squared_q_p_gt_q` (S7) | `q < p ∧ Nat.card G = p² · q → IsSolvable G` | Yes (Sylow + S5) |
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

Iteration 5 (PR #16972, merged) added the normal-Sylow reductions
(`burnside_pq_with_normal_pSylow`, `burnside_pq_with_normal_qSylow`).
Iteration 6 (PR #17035, merged) wrote a build-ready spec for `|G| = p² · q`.
Iteration 7 (this session) implements the spec's `p > q` half axiom-free.

1. **(S8)** Prove `burnside_p_squared_q_p_lt_q` axiom-free (Iteration 6
   spec §5, ~40 lines). Sylow analysis: `n_q ∣ p²` with three cases
   `{1, p, p²}`; `n_q = p` ruled out by `p < q`; `n_q = p²` requires
   `q ∣ p² - 1`, ruled out except for `(p, q) = (2, 3)`.
2. **(S9)** Prove `burnside_p_squared_q_twelve` exceptional case
   (Iteration 6 spec §6, ~70 lines). Element-counting: `n_3 = 4` ⇒
   8 elements of order 3 ⇒ unique Sylow 2-subgroup.
3. **(S10)** Combine into `burnside_p_squared_q` and graft into `burnside_pq`
   to remove the `(a, b) = (2, 1)` axiom dependency entirely.
4. **(S11+)** Symmetric `burnside_p_q_squared` (`|G| = p · q²`).
5. **(S12+)** `burnside_p_squared_q_squared` (`|G| = p² · q²`).
6. **(S13+)** Build Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`
   (~200-400 lines). Closes ALL remaining cases.
7. **(Final)** Replace `axiom burnside_pq_nontrivial` with theorem; sync meta.json;
   submit Mathlib upstream PR (~1000 lines total).
