# Problem: Eliminate `three_dvd_gal_card` via Dedekind's Theorem on Frobenius Elements

**Slug**: `inverse-galois-a5-oq-01`
**Parent**: `inverse-galois-a5` — *A₅ as a Galois Group over ℚ: The First
Non-Solvable Realization*. Status `axiomatized`, badge `axiom`, 0 sorries,
**1 axiom** (`three_dvd_gal_card`), 84 theorems, 2067 lines
(`proofs/Proofs/InverseGaloisA5.lean`).
**Sibling proofs**:
- `inverse-galois` (foundational), `inverse-galois-d4`, `inverse-galois-f20`
- The inverse-Galois OQ family for solvable groups (D4, F20, OQ01, OQ02, OQ06OQ01)

## Plain Statement

The parent file proves the inverse Galois problem for **A₅** — the smallest
non-solvable simple group — using the polynomial
`q(x) = x⁵ - 5x⁴ + 10x³ - 10x² + 25x - 5`. The proof that `|Gal(q/ℚ)| = 60`
proceeds in three steps:

1. **Upper bound**: `gal_card_dvd_60_proved` (Vandermonde discriminant chain,
   Part XV) — Disc(q) = 32000² is a perfect square ⇒ Gal ⊆ A₅ ⇒ |Gal| | 60.
2. **Five divides**: `five_dvd_gal_card` — q irreducible of degree 5 ⇒
   5 | |Gal| by Cauchy.
3. **Three divides** (`three_dvd_gal_card`, **AXIOM**): `q mod 7` factors as
   `(X-5)(X-6)(X³ + 6X² + 4X + 1)` with the cubic irreducible over `F₇`. By
   **Dedekind's theorem on Frobenius elements at prime ideals**, this
   factorisation pattern `(1, 1, 3)` implies `Gal` contains an element with a
   3-cycle, hence `3 ∣ |Gal|`.

Combined with `no_subgroup_order_15` and `no_subgroup_order_30`, these force
`|Gal| = 60`, and then `q_gal_iso_a5` gives `Gal ≅ A₅`.

**The open question** is to **prove** `three_dvd_gal_card` from Mathlib —
eliminating the last remaining axiom and upgrading the parent's status from
`axiomatized` to `verified` (badge `original`, axiomCount `0`).

The Lean statement of the axiom:

```lean
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal
```
(`Proofs/InverseGaloisA5.lean:309`)

## Why this Matters

1. **Axiom elimination on the only remaining axiom of a flagship proof.**
   The parent file already eliminated four other axioms during earlier
   sessions (Axioms A, C, D, and the original `q_gal_card`); the
   400-line Vandermonde discriminant chain in Parts VIII–XV is one of the
   project's largest single mechanical achievements. Closing
   `three_dvd_gal_card` finishes the job: the proof would be the **first
   non-solvable realisation of the inverse Galois problem to be fully
   verified in Lean** with `status: verified` and `badge: original`.

2. **First gallery-level Dedekind-theorem instance.**
   Dedekind's theorem (the factorisation of a monic separable polynomial
   modulo an unramified prime determines the cycle decomposition of the
   Frobenius automorphism on the integer ring) is **not in Mathlib**
   (pinned `v4.26.0`, May 2026). The OQ01 task is to bridge this gap **at
   least for the specialisation `(q, p) = (x⁵ - 5x⁴ + 10x³ - 10x² + 25x - 5, 7)`**.
   A full Mathlib-grade formalisation of Dedekind would also unlock
   axiom elimination in other Galois-theoretic gallery proofs
   (`abel-ruffini-galois-extensions`, `inverse-galois-d4` and its OQs,
   resolvent-sextic arguments, etc.).

3. **Mathlib upstream contribution path.**
   `Mathlib.NumberTheory.NumberField.Discriminant` and
   `Mathlib.NumberTheory.RamificationInertia` already contain the
   ramification/inertia framework; the missing piece is the explicit
   cycle-decomposition bridge to the Galois group of the splitting field.
   Even a specialised case (irreducible factor produces a cycle of that
   length) would be a publishable Mathlib PR.

4. **Two-source confidence on the axiom.**
   The parent file's docstring records that `three_dvd_gal_card` is
   supported by **two distinct computations** (`Proofs/InverseGaloisA5.lean`
   lines 870-878): (i) the mod-7 factorisation Dedekind argument; (ii) a
   resolvent-sextic argument ruling out subgroup orders dividing 20. Either
   route gives `3 ∣ |Gal|`. The OQ01 question allows either approach (the
   slug name privileges Dedekind, but the resolvent route would also
   close it).

## Mathematical Specification

### B.1 Dedekind's Theorem (Specialisation Needed)

> **Theorem (Dedekind).** Let `q(X) ∈ ℤ[X]` be a monic separable polynomial
> with splitting field `K = ℚ(α₁, …, αₙ)`. Let `O_K` be the ring of integers
> of `K`. Let `p` be a rational prime that does **not** divide `disc(q)`
> (hence is unramified in `O_K`). Suppose `q mod p` factors in `F_p[X]` as a
> product of distinct monic irreducibles of degrees `d₁ ≥ d₂ ≥ ⋯ ≥ d_k`.
> Then there exists a Frobenius element `σ ∈ Gal(K/ℚ)` whose action on
> `{α₁, …, αₙ}`, viewed as an element of `S_n`, has cycle type
> `(d₁, d₂, …, d_k)`.
>
> In particular, `Gal(K/ℚ)` contains an element of order `lcm(d₁, …, d_k)`.

For our specific case `(q, p) = (q, 7)`:
- `disc(q) = 32000² = 2¹⁴ · 5⁶ · 100 = 1024000000` — divisible by 2 and 5 but
  not by 7 ⇒ p = 7 is unramified ✓
- `q mod 7 = (X - 5)(X - 6)(X³ + 6X² + 4X + 1)` with the cubic irreducible
  over `F₇` (verified in `cubic_factor_no_roots_mod7`) ⇒ cycle type
  `(1, 1, 3)` ⇒ `Gal` contains an element of order 3 ⇒ `3 ∣ |Gal|`.

### B.2 Three Routes to Discharging `three_dvd_gal_card`

| Route | Strategy | Lean Effort | Mathlib PR Potential |
|-------|----------|-------------|----------------------|
| **R1** | **Specialised Dedekind**: prove the cycle-type→divisibility bridge **only for the q-at-7 case**, using the existing Part XII evidence (`q_root_mod7_at_5`, `q_root_mod7_at_6`, `cubic_factor_no_roots_mod7`) and a hand-built Frobenius element construction. | ~400 Lean lines | low — too specialised |
| **R2** | **General Dedekind**: formalise the full Dedekind theorem (Frobenius cycle decomposition) in Mathlib style and apply it once to discharge the axiom. | ~1500-2000 Lean lines | **HIGH** — landmark Mathlib PR |
| **R3** | **Resolvent-sextic substitute**: prove `3 ∣ |Gal|` by a completely different route — the cubic resolvent `R(q)` of `q` has no rational root, so `Gal(R(q)/ℚ)` is `S₃` (order 6, divisible by 3), and the natural map `Gal(q) → Gal(R(q))` is surjective. | ~600 Lean lines | medium |

R1 is the fastest path to gallery `verified` status. R2 is the
highest-leverage choice for the Lean ecosystem. R3 is the cleanest
"axiom-substitute" if R1's specialised Frobenius construction proves
too case-heavy.

### B.3 What Part XII Already Provides

The parent file's Part XII (lines 715-884) provides the **computational**
half of R1. The decidable verification of the mod-7 factorisation is
already in Lean:

| Existing decl | Line | Content |
|---------------|------|---------|
| `disc_value_is_square` | 779 | `(32000 : ℤ)^2 = 1024000000` (`norm_num`) |
| `trinomial_disc_computation` | 783 | `4⁴·20⁵ + 5⁵·16⁴ = 1024000000` (`norm_num`) |
| `q_root_mod7_at_5` | 787 | `q(5) ≡ 0 mod 7` (`decide`) |
| `q_root_mod7_at_6` | 791 | `q(6) ≡ 0 mod 7` (`decide`) |
| `cubic_factor_no_roots_mod7` | 796 | `X³ + 6X² + 4X + 1` has no roots in `F₇` (`decide`) |
| `q_mod7_factorization_pattern` (referenced) | nearby | informal documentation of the pattern |

The **missing** ingredients are the Frobenius construction (R1's
specialised version) or the full ramification-inertia bridge (R2's
generic version).

## Mathlib Infrastructure Map (pinned `v4.26.0`)

| Need | Mathlib Module | Status |
|------|----------------|--------|
| Number ring `O_K` of a number field | `Mathlib.NumberTheory.NumberField.Basic` | available |
| Discriminant of a number field / polynomial | `Mathlib.NumberTheory.NumberField.Discriminant`, `Mathlib.RingTheory.Discriminant` | available |
| Ramification / inertia indices | `Mathlib.NumberTheory.RamificationInertia.*` | available |
| Frobenius element in `Gal(K/ℚ)` at an unramified prime | `Mathlib.FieldTheory.Galois.Frobenius` (?) | **PARTIAL** — basic existence but no cycle-decomposition bridge |
| Cycle-type of `σ` acting on a set | `Mathlib.GroupTheory.Perm.Cycle.Type` | available |
| Factorisation of a polynomial mod p in `F_p[X]` | `Mathlib.RingTheory.UniqueFactorizationDomain` | available |
| **Dedekind's cycle-decomposition theorem** | — | **GAP** (the entire content of R2) |
| Resolvent cubic / sextic | — | **GAP** (the entire content of R3) |

## Reference Reading

| # | Source | Why |
|---|--------|-----|
| 1 | Dummit, D. S.; Foote, R. M. (2004). *Abstract Algebra* (3rd ed), §14.8 "Galois groups of polynomials". | Standard textbook treatment of Dedekind's theorem and the cycle-type-from-mod-p-factorisation principle. |
| 2 | Neukirch, J. (1999). *Algebraic Number Theory*, Theorem I.9.6 + §I.13. | Frobenius element and decomposition-inertia framework at unramified primes. |
| 3 | Lang, S. (1994). *Algebraic Number Theory* (2nd ed), §I.7 "The Decomposition Group". | Concise proof that `Frob_p` has the predicted cycle type. |
| 4 | Cohen, H. (1993). *A Course in Computational Algebraic Number Theory*, §6.4. | Algorithmic / computational view; useful for the specialised R1 construction. |
| 5 | Conrad, K. *Galois groups of cubics and quartics (not in characteristic 2)*. expository notes. | Resolvent cubic / sextic context for R3. |

## Proposed Decomposition

| Session | Phase | Target | Lines (est.) |
|---------|-------|--------|--------------|
| **S1 (this)** | OBSERVE | Survey: Dedekind's theorem, three routes (R1/R2/R3), Mathlib gap, parent's Part XII evidence. Markdown + JSON only. | 0 Lean / ~500 md+json |
| **S2** | ORIENT | **Recommended**: pick R1 (specialised). Draft a companion file `InverseGaloisA5Dedekind.lean` containing:<br>(a) the local-Frobenius construction at `p = 7`,<br>(b) a 3-cycle-witness `σ : Equiv.Perm (Fin 5)`,<br>(c) a single theorem `three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal` reducing the axiom. State the theorem with `sorry`; provide the Frobenius construction in skeleton form. | ~150 Lean (mostly sorry-filled) |
| **S3** | ACT | Discharge the Frobenius-construction sorries: explicit prime ideal `𝔭 ∣ 7` in `O_K`; decomposition group at `𝔭`; lift to `Gal(q)`; show the induced permutation has cycle type `(1,1,3)`. | ~400 Lean |
| **S4** | ACT (alt R3) | Backup route if R1 stalls: resolvent sextic construction; `Gal(q)` surjects onto a transitive subgroup of `S₃`; combine with no-order-15 to force 3 ∣ |Gal|. | ~600 Lean |
| **S5+** | CLOSE | Once `three_dvd_gal_card_proved` is verified: in `InverseGaloisA5.lean`, replace `axiom three_dvd_gal_card` with `theorem three_dvd_gal_card := three_dvd_gal_card_proved`. Update `src/data/proofs/inverse-galois-a5/meta.json`: `status: axiomatized → verified`, `badge: axiom → original`, `axiomCount: 1 → 0`. Build verify. | ~5 Lean diff + ~20 meta.json |

The S2-S3 pair (R1 specialised) is the minimum tractable formalisation
deliverable that achieves the gallery-status upgrade. S4 is a safety
valve if Frobenius construction at the chosen prime ideal `𝔭` turns out
to require deeper Mathlib infrastructure than currently available.

## Honest Calibration

- **R1 risk**: the specialised Frobenius construction requires picking a
  concrete prime ideal `𝔭 ∣ 7` in the (somewhat large) ring of integers
  of `q.SplittingField` and proving its decomposition group is generated
  by a 3-cycle on the roots. This is a routine but lengthy hand-derivation;
  expect Lean line counts on the high end of the estimate (~400-500).
- **R2 ambition vs scope**: a clean Dedekind-theorem Mathlib PR would
  resolve dozens of gallery axioms simultaneously. This is a 6-month
  ecosystem contribution, **not** a single-session gallery deliverable.
- **R3 backup viability**: the resolvent sextic of `q` is computable
  (~50 lines of `norm_num`); the surjection `Gal(q) → Gal(resolvent)` is
  the standard galois-correspondence argument (~100 lines once the resolvent
  is in hand). The order-3 element then comes from `S₃ ⊆ Gal(resolvent)`.

**The S1 OBSERVE output is doc-only — no Lean changes, no axiom delta.** This
is a survey iteration that prepares S2 (ORIENT) and S3 (ACT) for substantive
formalisation. Per the role doc's axiom-elimination priority, S2-S3 is
high-value work (eliminating the last axiom of a flagship proof).
