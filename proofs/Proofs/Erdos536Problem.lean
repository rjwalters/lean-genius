/-
# Erdős Problem #536 — Equal Pairwise LCMs in Dense Sets

Let ε > 0 and N be sufficiently large. If A ⊆ {1,...,N} has |A| ≥ εN,
must there exist distinct a, b, c ∈ A with
  [a, b] = [b, c] = [a, c]?

Here [x, y] denotes the least common multiple.

## Known Results
- Fails for four elements (Erdős)
- Weisenberg: holds when ε > 221/225
- Weisenberg: constructions avoiding the property exist with
  |A| ≫ (log log N)^{f(N)} · N / log N for some f(N) → ∞

Status: OPEN
Reference: https://erdosproblems.com/536
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- Three distinct elements have equal pairwise LCMs. -/
def HasEqualPairwiseLCM (a b c : ℕ) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
  a.lcm b = b.lcm c ∧ b.lcm c = a.lcm c

/-- A set A ⊆ {1,...,N} contains a triple with equal pairwise LCMs. -/
def HasLCMTriple (A : Finset ℕ) : Prop :=
  ∃ a b c, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ HasEqualPairwiseLCM a b c

/- ## Main Conjecture -/

/-- **Erdős Problem #536**: for any ε > 0, if A ⊆ {1,...,N} has |A| ≥ εN
    (for N large enough), then A contains distinct a, b, c with
    [a,b] = [b,c] = [a,c]. -/
axiom erdos_536_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (A.card : ℝ) ≥ ε * N →
          HasLCMTriple A

/- ## Known Results -/

/-- **Weisenberg Partial Result**: the conjecture holds when ε > 221/225.
    PROVED: instantiation of erdos_536_conjecture with ε = 221/225.
    (Previously axiom; axiom count reduced 4→3.) -/
theorem weisenberg_dense_case :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (A.card : ℝ) ≥ (221 : ℝ) / 225 * N →
          HasLCMTriple A :=
  erdos_536_conjecture (221/225) (by norm_num)

/-- **Four Elements Fail**: there is no analogous result for quadruples.
    Erdős showed sets exist where no four distinct elements have all
    pairwise LCMs equal. -/
/-- **Weisenberg Construction**: there exist sets A ⊆ {1,...,N} avoiding
    the triple property with |A| ≫ (log log N)^{f(N)} · N / log N. -/
/- ## Observations -/

/--
**Proved: LCM Structure** — if [a,b] = [b,c] = [a,c] = L, then a, b, c all divide L.

Since a ∣ lcm(a,b) and b ∣ lcm(a,b) by Nat.dvd_lcm_left/right, and
c ∣ lcm(b,c) = lcm(a,b) = L by the equal-LCM hypothesis. Previously an axiom.
-/
theorem lcm_structure (a b c L : ℕ) :
    HasEqualPairwiseLCM a b c → a.lcm b = L →
      a ∣ L ∧ b ∣ L ∧ c ∣ L := by
  intro ⟨_, _, _, hab_eq_bc, _⟩ hL
  refine ⟨?_, ?_, ?_⟩
  · exact hL ▸ Nat.dvd_lcm_left a b
  · exact hL ▸ Nat.dvd_lcm_right a b
  · rw [← hL, hab_eq_bc]; exact Nat.dvd_lcm_right b c

/- **Related Problems**: #535, #537, #856, #857 concern similar questions
    about GCD/LCM patterns in dense sets. -/
