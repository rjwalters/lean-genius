import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Toward Burnside's `pᵃqᵇ` Theorem: Verified Reduction Scaffolding

## The Target

**Burnside's `pᵃqᵇ` theorem** (1904): every finite group whose order has the form
`pᵃ · qᵇ` for primes `p`, `q` is **solvable**. Equivalently, a finite simple group
whose order has at most two distinct prime factors is cyclic of prime order.

The only known proofs of the full statement go through the **character theory of
finite groups** (the "elementary" group-theoretic proofs found decades later still
rely on substantial machinery). The character-theoretic heart is:

* the degrees of the irreducible complex representations divide `|G|`;
* an algebraic-integer argument (Burnside's vanishing lemma): if a conjugacy class
  has size coprime to `χ(1)` for an irreducible character `χ`, then `χ(g) = 0` or
  the representation is scalar at `g`;
* counting irreducibles by conjugacy classes;

which together force a finite nonabelian group of order `pᵃqᵇ` to possess a proper
nontrivial normal subgroup. Solvability then follows by induction.

## What This File Provides (all fully verified, no `sorry`, no `axiom`)

Mathlib currently has the *outer* layers of this argument but **not** the
character-theoretic core. This file assembles the verified outer layers into the
two reusable ingredients that any proof of Burnside's theorem ultimately needs:

1. `isSolvable_of_isPGroup` / `isSolvable_of_card_prime_pow` — the **base case**:
   groups of prime-power order are solvable (they are even nilpotent). This is the
   `b = 0` (and `a = 0`) edge of the `pᵃqᵇ` grid, and the leaves of the induction.
2. `solvable_of_normal_extension` — the **inductive step engine**: an extension of a
   solvable group by a solvable group is solvable. Given a proper nontrivial normal
   subgroup `N`, solvability of `N` and of `G ⧸ N` yields solvability of `G`.

With these two in hand, Burnside's theorem reduces to the single purely
group-theoretic statement
  *"a finite nonabelian group of order `pᵃqᵇ` is not simple"*,
which is exactly the part still missing from Mathlib (it is the character-theory
core above). We record that reduction precisely as `burnside_reduces_to_nonsimplicity`
below — a *conditional* theorem that takes the non-simplicity fact as an explicit
hypothesis and is itself fully verified.

## Mathlib Dependencies

- `IsPGroup.of_card`, `IsPGroup.isNilpotent` : prime-power groups are nilpotent
- `IsNilpotent.to_isSolvable` : nilpotent ⟹ solvable
- `solvable_of_ker_le_range` : the homological extension principle for solvability
- `QuotientGroup.ker_mk'`, `Subgroup.range_subtype` : identifying kernel and range

## Status

`verified` — every declaration is machine-checked with no `sorry` and no `axiom`.
The full `pᵃqᵇ` theorem is *not* claimed here; it is documented as the open frontier
and reduced to a single hypothesis. See `research/problems/.../knowledge.md`.
-/

open Subgroup

namespace BurnsidePaQb

variable {G : Type*} [Group G]

/-! ### Base case: prime-power order ⟹ solvable -/

/-- A finite `p`-group is solvable (indeed nilpotent). This is the leaf case of the
inductive proof of Burnside's theorem and the `a = 0`/`b = 0` edge of the grid. -/
theorem isSolvable_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (h : IsPGroup p G) : IsSolvable G := by
  haveI := h.isNilpotent
  infer_instance

/-- A finite group of prime-power order `pⁿ` is solvable. -/
theorem isSolvable_of_card_prime_pow [Finite G] {p n : ℕ} [Fact p.Prime]
    (h : Nat.card G = p ^ n) : IsSolvable G :=
  isSolvable_of_isPGroup (IsPGroup.of_card h)

/-! ### Inductive step: extensions of solvable groups are solvable -/

/-- **Extension principle for solvability.** If `N` is a normal subgroup of `G` with
both `N` and the quotient `G ⧸ N` solvable, then `G` is solvable.

This is the engine of the induction in Burnside's theorem: a proper nontrivial
normal subgroup splits `G` into two strictly smaller pieces, each of order again of
the form `pᵃqᵇ`, to which the induction hypothesis applies. -/
theorem solvable_of_normal_extension (N : Subgroup G) [N.Normal]
    [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-! ### The reduction to non-simplicity

We package the two-prime hypothesis as a predicate on the order, closed under passing
to subgroups and quotients (since their orders divide `|G|`). -/

/-- `OrderTwoPrimes p q G` says every prime divisor of `|G|` is `p` or `q`; equivalently
`|G|` has the form `pᵃqᵇ`. This is the hypothesis class of Burnside's theorem and is
inherited by subgroups and quotients. -/
def OrderTwoPrimes (p q : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q

/-- **Burnside's theorem, reduced to a single group-theoretic input.**

If one supplies the (character-theoretic, currently not in Mathlib) fact that *every*
finite nonabelian group whose order involves only the primes `p`, `q` has a proper
nontrivial normal subgroup, then every finite group of order `pᵃqᵇ` is solvable.

This theorem is fully verified: it performs the strong induction on `|G|` and the
extension assembly, isolating the unproved mathematics into the single hypothesis
`not_simple`. Discharging `not_simple` from Mathlib would complete Burnside's theorem. -/
theorem burnside_reduces_to_nonsimplicity {p q : ℕ}
    (not_simple : ∀ (H : Type) [Group H] [Finite H], OrderTwoPrimes p q H →
      Nontrivial H → (¬ ∀ a b : H, a * b = b * a) →
      ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤) :
    ∀ (H : Type) [Group H] [Finite H], OrderTwoPrimes p q H → IsSolvable H := by
  -- Strong induction on the order `n = |H|`, phrased so the hypothesis applies to the
  -- subgroup `N` and quotient `H ⧸ N` (both genuine `Type`s of strictly smaller order).
  have key : ∀ n : ℕ, ∀ (H : Type) [Group H] [Finite H],
      Nat.card H = n → OrderTwoPrimes p q H → IsSolvable H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H _ _ hcard htp
      -- Abelian groups are solvable outright; otherwise invoke non-simplicity.
      by_cases hcomm : ∀ a b : H, a * b = b * a
      · exact isSolvable_of_comm hcomm
      · -- A nonabelian group is nontrivial.
        have hnt : Nontrivial H := by
          rcases subsingleton_or_nontrivial H with hs | hnt
          · exact absurd (fun a b => Subsingleton.elim (a * b) (b * a)) hcomm
          · exact hnt
        obtain ⟨N, hNnorm, hNbot, hNtop⟩ := not_simple H htp hnt hcomm
        haveI : N.Normal := hNnorm
        -- `N ≠ ⊤` gives `|N| < |H|`; `N ≠ ⊥` gives `|H ⧸ N| < |H|`.
        have hNlt : Nat.card N < Nat.card H := by
          have hidx : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNtop
          calc Nat.card N < Nat.card N * N.index :=
                (Nat.lt_mul_iff_one_lt_right Nat.card_pos).2 hidx
            _ = Nat.card H := Subgroup.card_mul_index N
        have hQlt : Nat.card (H ⧸ N) < Nat.card H := by
          rw [← Subgroup.index_eq_card N]
          have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
          have hcard1 : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.2 hNbot
          calc N.index < N.index * Nat.card N :=
                (Nat.lt_mul_iff_one_lt_right hpos).2 hcard1
            _ = Nat.card H := Subgroup.index_mul_card N
        -- Orders of `N` and `H ⧸ N` divide `|H|`, so they still involve only `p`, `q`.
        have hNdvd : Nat.card N ∣ Nat.card H := Subgroup.card_subgroup_dvd_card N
        have hQdvd : Nat.card (H ⧸ N) ∣ Nat.card H := Subgroup.card_quotient_dvd_card N
        have htpN : OrderTwoPrimes p q N := fun r hr hrd => htp r hr (hrd.trans hNdvd)
        have htpQ : OrderTwoPrimes p q (H ⧸ N) := fun r hr hrd => htp r hr (hrd.trans hQdvd)
        -- Apply the induction hypothesis to both strictly smaller pieces.
        haveI : IsSolvable N := ih _ (hcard ▸ hNlt) N rfl htpN
        haveI : IsSolvable (H ⧸ N) := ih _ (hcard ▸ hQlt) (H ⧸ N) rfl htpQ
        -- Reassemble via the extension principle.
        exact solvable_of_normal_extension N
  intro H _ _ htp
  exact key (Nat.card H) H rfl htp

end BurnsidePaQb
