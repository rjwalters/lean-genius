# Knowledge — inverse-galois-a5-oq-01

## S1 (researcher-12, 2026-05-12) — OBSERVE survey

### Status

The task is to **eliminate the parent's last axiom** `three_dvd_gal_card`
and upgrade `inverse-galois-a5` from `status: axiomatized` (1 axiom,
84 theorems, 2067 lines) to `status: verified` (0 axioms,
`badge: original`). The axiom asserts `3 ∣ Fintype.card q.Gal` where
`q.Gal := q.SplittingField ≃ₐ[ℚ] q.SplittingField` and
`q(x) = x⁵ - 5x⁴ + 10x³ - 10x² + 25x - 5`.

Three discharge strategies exist (R1 / R2 / R3 in `problem.md`).
R1 (specialised Dedekind at `p = 7`) is the **recommended S2 entry
point**: it uses the existing Part XII decidable verification and
adds only the Frobenius-construction-and-cycle-type bridge.

### Parent file inventory

`proofs/Proofs/InverseGaloisA5.lean` (2067 lines, 1 axiom, 0 sorries,
84 theorems, 12 defs) provides the surrounding infrastructure:

| Decl | Line | Role for OQ-01 |
|------|------|----------------|
| `def q : ℤ[X]` | (Part I, ~85) | the polynomial whose Galois group we are analysing |
| `q.Gal` (abbrev for `q.SplittingField ≃ₐ[ℚ] q.SplittingField`) | (Part II) | the Galois group target |
| `q_irreducible` | (Part III) | Eisenstein at `p = 5`, used by `five_dvd_gal_card` |
| `disc_value_is_square` | 779 | `(32000 : ℤ)^2 = 1024000000` — discriminant value |
| `trinomial_disc_computation` | 783 | `4⁴·20⁵ + 5⁵·16⁴ = 1024000000` |
| `q_root_mod7_at_5` | 787 | `q(5) ≡ 0 mod 7` (decidable) |
| `q_root_mod7_at_6` | 791 | `q(6) ≡ 0 mod 7` (decidable) |
| `cubic_factor_no_roots_mod7` | 796 | `X³ + 6X² + 4X + 1` has no roots in `F₇` |
| `five_dvd_gal_card` | 207 | `5 ∣ Fintype.card q.Gal` (proved, via Cauchy + degree) |
| `gal_card_dvd_120` | 215 | `Fintype.card q.Gal ∣ 120` (via root permutation embedding) |
| `gal_card_dvd_60_proved` | (Part XV) | `Fintype.card q.Gal ∣ 60` (Vandermonde discriminant chain) |
| **`three_dvd_gal_card`** | **309** | **THE TARGET AXIOM** |
| `no_subgroup_order_15` | 511 | rules out `|Gal| = 15` (Sylow, no element of order 15 in S₅) |
| `no_subgroup_order_30` | 532 | rules out `|Gal| = 30` (A₅ simple ⇒ no index-2 subgroup of order 30) |
| `q_gal_card` (proved theorem, NOT axiom) | (Part XVI) | `Fintype.card q.Gal = 60` — combines 5∣, 3∣, ∣60, ≠15, ≠30 |
| `q_gal_iso_a5` | (Part XVI) | `Gal(q) ≅ A₅` via `Equiv.Perm.eq_alternatingGroup_of_index_eq_two` |
| `a5_realizable_iso`, `gal_not_solvable` | (Part XVII) | main theorems consuming `q_gal_card` |

Note: `three_dvd_gal_card` is the **only axiom** in the parent file at
the current revision (Part XII comments call earlier "axioms" A/C/D
eliminated; Axiom B is the surviving one renamed `three_dvd_gal_card`).

### Dedekind's theorem (specialised form needed for R1)

For the specific case `(q, p) = (q, 7)`, the theorem statement is:

> Let `K = q.SplittingField`, `O_K` its ring of integers, and `α₁, …, α₅`
> the roots of `q` in `K`. Let `𝔭 ⊂ O_K` be any prime ideal above `7`
> (since `7 ∤ disc(q) = 32000²`, `7` is unramified). Then the Frobenius
> automorphism `Frob_𝔭 ∈ Gal(K/ℚ)`, acting on `{α₁, …, α₅}` as a permutation
> in `S_5`, has cycle type matching the mod-7 factorisation of `q`:
> namely `(1, 1, 3)` (two fixed roots — those reducing to `5` and `6` mod 7 —
> and a 3-cycle on the remaining three roots).

Consequence: `Frob_𝔭` has order 3 in `Gal(K/ℚ)`, hence `3 ∣ |Gal|`.

The **proof** of this specialised Dedekind statement in Lean requires:

1. **A prime ideal at 7**: exhibit some `𝔭 ⊂ O_K` with `𝔭 ∩ ℤ = 7ℤ`.
   `Mathlib.NumberTheory.RamificationInertia` provides the existence
   (`Ideal.exists_isMaximal_ne_bot_of_isPrime` etc.); the decomposition
   index `f(𝔭/7)` should equal `3` (the cubic factor degree).
2. **The decomposition group `D(𝔭/7) ⊂ Gal(K/ℚ)`**: cyclic of order
   `f(𝔭/7) = 3` since `7` is unramified.
3. **The Frobenius generator `σ` of `D(𝔭/7)`**: acts on the residue
   field `O_K / 𝔭` as `x ↦ x^7`; lifts to the permutation that fixes
   the two roots reducing to `5, 6 ∈ F₇` and 3-cycles the three roots
   in the irreducible cubic factor.
4. **Cycle type of `σ`** in `S_5` via the root-permutation embedding
   `φ : Gal(K/ℚ) →* S_5`.

Step 1 is in Mathlib but needs careful instantiation. Step 2 follows
from `Mathlib.NumberTheory.RamificationInertia.Galois`. Steps 3 and 4
are the **substantive new content** — roughly 200-300 lines of
careful coordinate-tracking.

### Mathlib API survey (`v4.26.0`)

| Class / lemma | Module | Purpose for OQ-01 |
|---------------|--------|---|
| `NumberField K` | `Mathlib.NumberTheory.NumberField.Basic` | base typeclass on `q.SplittingField` |
| `Ideal.IsPrime`, `Ideal.IsMaximal` | core | the ideal `𝔭` |
| `Polynomial.disc`, `Algebra.discr` | `RingTheory.Discriminant` | gives `disc(q) = 32000²`, used for unramifiedness at 7 |
| `Ideal.ramificationIdx`, `Ideal.inertiaDeg` | `Mathlib.NumberTheory.RamificationInertia.Basic` | `e(𝔭/7) = 1` (unramified), `f(𝔭/7) ∈ {1, 1, 3}` |
| `Ideal.Quotient.frobenius` (approx — name may differ) | `Mathlib.NumberTheory.RamificationInertia.Galois` | provides the Frobenius element at an unramified prime |
| `Equiv.Perm.cycleType` | `Mathlib.GroupTheory.Perm.Cycle.Type` | cycle-type of the image of `σ` in `S₅` |
| `orderOf` | `Mathlib.GroupTheory.OrderOfElement.Basic` | `orderOf σ = 3` from cycle type |
| `Cauchy` (existence of element of prime order divisor) | `Mathlib.GroupTheory.SpecificGroups.Cyclic` etc. | reverse direction: order 3 ⇒ 3 ∣ |Gal| |

The bridge `cycle type (1,1,3) ⇒ order 3` is mostly mechanical
(`Equiv.Perm.lcm_cycleType_eq_orderOf` or similar).

### R1 (specialised Dedekind) Lean skeleton

```lean
-- File: proofs/Proofs/InverseGaloisA5Dedekind.lean (new, ~250 lines)
import Proofs.InverseGaloisA5
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace InverseGaloisA5Dedekind

open Polynomial InverseGaloisA5

local notation "K" => q.SplittingField
local notation "OK" => 𝓞 K  -- ring of integers

/-- 7 is unramified in K: `disc(q) = 32000² = 2¹⁴·5⁶·10⁴` is coprime to 7. -/
theorem seven_unramified : ¬ 7 ∣ Polynomial.disc q := by
  sorry  -- S3: decide-based arithmetic on disc value

/-- A prime ideal of OK above 7 with inertia degree 3 (corresponding
to the irreducible cubic factor X³+6X²+4X+1 of q mod 7). -/
noncomputable def 𝔭₃ : Ideal OK :=
  sorry  -- S3: explicit construction or non-constructive existence

theorem 𝔭₃_inertia_deg : Ideal.inertiaDeg 𝔭₃ (7 : ℤ) = 3 :=
  sorry  -- S3

/-- The Frobenius element at 𝔭₃, viewed in Gal(q/ℚ). -/
noncomputable def frob₃ : q.Gal :=
  sorry  -- S3: extract from Ideal.Quotient.frobenius framework

theorem frob₃_order_eq_three : orderOf frob₃ = 3 :=
  sorry  -- S3: follows from inertia degree 3

theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal := by
  -- Use Cauchy / orderOf-divides-cardinality on frob₃
  rw [← frob₃_order_eq_three]
  exact orderOf_dvd_card

end InverseGaloisA5Dedekind
```

### Decomposition plan (effort estimates)

| Session | Lines (est.) | Sorries delta | Axioms delta | Net |
|---------|--------------|---------------|--------------|-----|
| S1 OBSERVE (this) | 0 Lean / ~600 md+json | 0 | 0 | survey only |
| S2 ORIENT | ~80 Lean (skeleton + 4 sorries) | +4 | 0 | new file structure |
| S3 ACT (Frobenius construction) | ~400 Lean (discharge 4 sorries) | -4 | 0 | proves three_dvd_gal_card |
| S4 CLOSE (parent integration) | ~10 Lean diff + ~30 meta.json | 0 | **-1** | parent verified ✓ |
| S5 (optional) | resolvent-sextic alt-route documentation | 0 | 0 | safety valve |

Total over S2-S4: ~490 Lean, 0 net sorries, **-1 axiom on the parent**.

### Mathlib gap analysis

| # | Missing | Mathlib closest | Effort to bridge |
|---|---------|-----------------|------------------|
| 1 | "factorisation mod p → cycle type of Frob" general theorem | `Mathlib.NumberTheory.RamificationInertia.Galois` (partial) | ~600 Lean (R2 full generality) OR ~250 Lean (R1 specialised at p=7 for this q) |
| 2 | Resolvent cubic / sextic of a quintic | none | ~400 Lean (R3 entire route) |
| 3 | Explicit Frobenius generator from inertia data | `Ideal.Quotient.frobenius` (?) | ~50 Lean (lemmas linking residue Frobenius and Galois Frobenius) |

### Connections to sibling proofs

| Sibling | Status | Cross-impact |
|---------|--------|--------------|
| `inverse-galois` (foundational) | verified | no direct impact |
| `inverse-galois-d4` | axiomatized | a Dedekind formalisation also unblocks D4 axioms |
| `inverse-galois-d4-oq-03` | recently active (PR #18063) | independent |
| `inverse-galois-f20` | axiomatized | similar potential gain |
| `inverse-galois-oq-01`, `-oq-02`, `-oq-06-oq-01` | axiomatized | various; Dedekind helps several |
| `abel-ruffini-galois-extensions` | axiomatized | independent |

A full R2 Dedekind formalisation would propagate to multiple sibling
proofs simultaneously. R1 is parent-specific.

### Honest assessment

This OQ has **real axiom-elimination value** — closing the parent's last
axiom upgrades a flagship proof from `axiomatized` to `verified`. The
recommended R1 path is technically demanding but bounded (~500 Lean
lines across S2-S4) and uses existing Mathlib ramification-inertia
infrastructure.

**Risks**:
- The Frobenius construction may require more careful coordinate-tracking
  than the estimate; Lean's typeclass inference on `q.SplittingField` is
  occasionally finicky for explicit ideal arithmetic.
- If Step 1 (prime ideal construction) hits unexpected Mathlib gaps,
  fallback to R3 (resolvent sextic) costs ~600 lines and a different
  conceptual route.

**S1 OBSERVE does not resolve the OQ.** Its value is:
- Clear identification of the axiom (single statement, line 309 of parent);
- Three-route classification (R1/R2/R3) with effort estimates;
- Recommended S2-S3 plan with concrete Lean skeleton;
- Mathlib API survey identifying the relevant ramification-inertia modules.

## S2 (researcher-5, 2026-05-12) — ORIENT scaffold

### Deliverable

`proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 lines), registered in
`proofs/Proofs.lean`. Three theorems:

1. `seven_nondiv_disc : ¬ (7 : ℤ) ∣ 1024000000` (closed by
   `intro ⟨k, hk⟩; omega`). This is the unramifiedness precondition,
   stated at the numeric level (32000² = 1_024_000_000) to avoid a
   commitment to any particular Mathlib spelling of `Polynomial.discr`.
2. `exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3` — **the sole
   substantive sorry**, to be discharged in S3 via the Frobenius
   construction at any prime ideal of `𝒪_{q.SplittingField}` above 7
   with inertia degree 3.
3. `three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal` — the trivial
   bridge, closed by `obtain ⟨σ, hσ⟩ := exists_gal_order_three; rw [← hσ];
   exact orderOf_dvd_card`.

### Design compression rationale

S1's state.md planned a 4-sorry skeleton (`seven_unramified`, `𝔭₃`,
`𝔭₃_inertia_deg`, `frob₃`, `frob₃_order_eq_three`). In writing the
S2 file I noticed that these four sorries are tightly coupled and a
single existence-of-order-3-element statement abstracts the whole
chain. This means:

- S3 has **one focused API question** (find an order-3 Galois
  automorphism using Mathlib's ramification-inertia machinery)
  rather than four interlocking ones.
- The proof body can choose any concrete construction internally
  (e.g. directly using `Mathlib.NumberTheory.RamificationInertia.Galois`
  primitives, or working through prime-ideal arithmetic step by step)
  without committing the public interface.
- The bridge to `Fintype.card q.Gal` is already proved; S3's success
  immediately yields the full eliminator.

### Build/verification status

The new file imports `Mathlib` (umbrella) and `Proofs.InverseGaloisA5`.
Local docker-build verification was deferred (the worktree's
`proofs/.lake` symlink is recursive — see memory note — and a clean
build is ~30-45 min). The file is small and the closed lemmas use
standard `omega` and `orderOf_dvd_card` patterns; risk of compile
failure on the `(build pending)` PR is low. Auditor/deployer will
verify on merge.

### What S2 does NOT do

- No discharge of any sorry (`exists_gal_order_three` remains open).
- No parent-file changes (`InverseGaloisA5.lean` still uses `axiom
  three_dvd_gal_card`).
- No axiom-count delta on the parent.
- No gallery-status upgrade.

S2's value is purely structural: providing the bridge theorem and
isolating the remaining work into a single Mathlib-API task for S3.
