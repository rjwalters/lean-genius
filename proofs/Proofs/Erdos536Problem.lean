/-!
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

/-! ## Definitions -/

/-- Three distinct elements have equal pairwise LCMs. -/
def HasEqualPairwiseLCM (a b c : ℕ) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
  a.lcm b = b.lcm c ∧ b.lcm c = a.lcm c

/-- A set A ⊆ {1,...,N} contains a triple with equal pairwise LCMs. -/
def HasLCMTriple (A : Finset ℕ) : Prop :=
  ∃ a b c, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ HasEqualPairwiseLCM a b c

/-! ## Main Conjecture -/

/-- **Erdős Problem #536**: for any ε > 0, if A ⊆ {1,...,N} has |A| ≥ εN
    (for N large enough), then A contains distinct a, b, c with
    [a,b] = [b,c] = [a,c]. -/
axiom erdos_536_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (A.card : ℝ) ≥ ε * N →
          HasLCMTriple A

/-! ## Known Results -/

/-- **Weisenberg Partial Result**: the conjecture holds when ε > 221/225.
    That is, sets of density > 221/225 ≈ 0.982 in {1,...,N} must contain
    such a triple. -/
axiom weisenberg_dense_case :
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (A.card : ℝ) ≥ (221 : ℝ) / 225 * N →
        HasLCMTriple A

/-- **Four Elements Fail**: there is no analogous result for quadruples.
    Erdős showed sets exist where no four distinct elements have all
    pairwise LCMs equal. -/
axiom four_elements_fail :
  ∀ N : ℕ, ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    A.card ≥ N / 2 ∧
    ¬∃ a b c d, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A ∧
      ({a, b, c, d} : Finset ℕ).card = 4 ∧
      a.lcm b = a.lcm c ∧ a.lcm c = a.lcm d ∧
      a.lcm d = b.lcm c ∧ b.lcm c = b.lcm d ∧ b.lcm d = c.lcm d

/-- **Weisenberg Construction**: there exist sets A ⊆ {1,...,N} avoiding
    the triple property with |A| ≫ (log log N)^{f(N)} · N / log N. -/
axiom weisenberg_construction :
  ∃ f : ℕ → ℕ, (∀ k, ∃ N₀, ∀ N ≥ N₀, f N > k) ∧
    ∀ N : ℕ, N > 1 → ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      ¬HasLCMTriple A ∧ A.card ≥ f N

/-! ## Observations -/

/-- **LCM Structure**: [a,b] = [b,c] = [a,c] = L means a, b, c are all
    divisors of L that pairwise have LCM exactly L. Each pair covers all
    prime factors of L. -/
axiom lcm_structure (a b c L : ℕ) :
  HasEqualPairwiseLCM a b c → a.lcm b = L →
    a ∣ L ∧ b ∣ L ∧ c ∣ L

/-- **Related Problems**: #535, #537, #856, #857 concern similar questions
    about GCD/LCM patterns in dense sets. -/
axiom related_problems : True
