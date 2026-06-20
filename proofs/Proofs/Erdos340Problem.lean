/-
# Erdős Problem #340 — Growth of the Greedy Sidon Sequence

The greedy Sidon sequence (Mian–Chowla sequence) is A = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, ...}:
start with 1, then iteratively include the smallest integer preserving
the Sidon property (no non-trivial solutions to a + b = c + d).

**Conjecture:** |A ∩ {1,...,N}| ≫ N^{1/2 - ε} for all ε > 0.

**Status: OPEN.**

Known: trivial lower bound Ω(N^{1/3}). The sequence is OEIS A005282.
Erdős and Graham also asked whether A - A has positive density.

Reference: https://erdosproblems.com/340
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Filter Finset

/- ## Core Definitions -/

/-- A Sidon set (B₂ set): all pairwise sums a + b (a ≤ b, a,b ∈ S) are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- The greedy Sidon sequence: a(0) = 1, a(n+1) is the smallest integer
    not in {a(0),...,a(n)} such that adding it preserves the Sidon property. -/
noncomputable def greedySidon : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf { m : ℕ | m > greedySidon n ∧
      IsSidonSet ((Finset.range (n + 1)).attach.image (fun k => greedySidon k.1) ∪ {m}) }
  decreasing_by
    · exact Nat.lt_succ_self n
    · exact Finset.mem_range.mp k.2

/-- The counting function: |A ∩ {1,...,N}|. -/
noncomputable def greedySidonCount (N : ℕ) : ℕ :=
  (Finset.range N).filter (fun k => greedySidon k ≤ N) |>.card

/- ## Known Initial Values (OEIS A005282) -/

/-- The first 11 terms of the Mian-Chowla sequence match OEIS A005282:
    1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97. -/
axiom greedy_sidon_values :
    greedySidon 0 = 1 ∧ greedySidon 1 = 2 ∧ greedySidon 2 = 4 ∧
    greedySidon 3 = 8 ∧ greedySidon 4 = 13 ∧ greedySidon 5 = 21 ∧
    greedySidon 6 = 31 ∧ greedySidon 7 = 45 ∧ greedySidon 8 = 66 ∧
    greedySidon 9 = 81 ∧ greedySidon 10 = 97

/- ## Basic Properties

The two structural facts — that the greedy sequence is **strictly increasing** and
that every prefix is a **Sidon set** — used to be axioms here.  They are in fact
*theorems* about the `sInf`-based definition above, the only ingredient being that the
defining set is always nonempty, i.e. a finite Sidon set can always be extended.  We
prove this with the explicit witness `m = 2 · (sup A) + 1`: it lies strictly above
every element of `A`, so on each side of a putative collision `a + b = c + d` the new
element (if present) is the larger summand, and a band/parity count forces both sides
to use `m` equally often — after which `Nat` cancellation and the original Sidon
property close the gap.  (Same witness as the constructive existence kernel in
`Erdos340GreedySidonExtension.lean`.)

The recursion uses `(range (n+1)).attach.image (fun k => greedySidon k.1)` so that the
self-reference is visibly applied to indices `k.1 < n + 1` (this is what lets Lean's
termination checker accept the well-founded recursion); `attach_image_eq` identifies
this with the cleaner `Finset.image greedySidon (range (n+1))`, and
`greedySidon_succ_eq` is the resulting unfolding lemma for `greedySidon (n + 1)`. -/

/-- The `attach`-guarded prefix image used inside the definition coincides with the
ordinary `Finset.image greedySidon (range (n+1))`. -/
theorem attach_image_eq (n : ℕ) :
    (Finset.range (n + 1)).attach.image (fun k => greedySidon k.1)
      = Finset.image greedySidon (Finset.range (n + 1)) := by
  conv_rhs => rw [← Finset.attach_image_val (s := Finset.range (n + 1))]
  rw [Finset.image_image]
  rfl

/-- Unfolding lemma for the successor step, stated with the clean prefix image. -/
theorem greedySidon_succ_eq (n : ℕ) :
    greedySidon (n + 1) = sInf { m : ℕ | m > greedySidon n ∧
      IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)) ∪ {m}) } := by
  conv_lhs => rw [greedySidon]
  rw [attach_image_eq]

/-- **Extension lemma.** Inserting the explicit witness `2 · sup A + 1` into a Sidon
set keeps it Sidon: the witness sits strictly above every element of `A`. -/
theorem isSidonSet_insert_two_sup_add_one {A : Finset ℕ} (hA : IsSidonSet A) :
    IsSidonSet (insert (2 * A.sup id + 1) A) := by
  set S := A.sup id with hS
  set m := 2 * S + 1 with hm
  have hbound : ∀ x ∈ A, x ≤ S := fun x hx => Finset.le_sup (f := id) hx
  intro a ha b hb c hc d hd hab hcd hsum
  simp only [Finset.mem_insert] at ha hb hc hd
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;>
    rcases hc with rfl | hc <;> rcases hd with rfl | hd <;>
  first
    | exact hA a ha b hb c hc d hd hab hcd hsum
    | (try have ba := hbound _ ha
       try have bb := hbound _ hb
       try have bc := hbound _ hc
       try have bd := hbound _ hd
       omega)

/-- The set of admissible next values for the greedy sequence — the one whose `sInf`
defines `greedySidon (n + 1)` — is nonempty, witnessed by `2 · sup(prefix) + 1`. -/
theorem greedy_defining_set_nonempty (n : ℕ)
    (hP : IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)))) :
    { m : ℕ | m > greedySidon n ∧
      IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)) ∪ {m}) }.Nonempty := by
  set P := Finset.image greedySidon (Finset.range (n + 1)) with hPdef
  refine ⟨2 * P.sup id + 1, ?_, ?_⟩
  · have hmem : greedySidon n ∈ P := by
      rw [hPdef]; exact Finset.mem_image_of_mem _ (Finset.self_mem_range_succ n)
    have hle : greedySidon n ≤ P.sup id := Finset.le_sup (f := id) hmem
    omega
  · have heq : P ∪ {2 * P.sup id + 1} = insert (2 * P.sup id + 1) P := by
      rw [Finset.union_comm, Finset.insert_eq]
    rw [heq]
    exact isSidonSet_insert_two_sup_add_one hP

/-- The defining `sInf` is attained: `greedySidon (n + 1)` lies in its admissible set,
hence it is `> greedySidon n` and extends the prefix to a Sidon set. -/
theorem greedySidon_succ_spec (n : ℕ)
    (hP : IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)))) :
    greedySidon (n + 1) > greedySidon n ∧
      IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)) ∪ {greedySidon (n + 1)}) := by
  have h := Nat.sInf_mem (greedy_defining_set_nonempty n hP)
  rw [Set.mem_setOf_eq] at h
  rw [greedySidon_succ_eq]
  exact h

/-- Every prefix of the greedy sequence forms a valid Sidon set.  (Was an axiom.) -/
theorem greedy_sidon_is_sidon : ∀ n : ℕ,
    IsSidonSet (Finset.image greedySidon (Finset.range (n + 1))) := by
  intro n
  induction n with
  | zero =>
      have hsingle : Finset.image greedySidon (Finset.range (0 + 1)) = {greedySidon 0} := by
        simp [Finset.range_one]
      rw [hsingle]
      intro a ha b hb c hc d hd _ _ _
      simp only [Finset.mem_singleton] at ha hb hc hd
      subst ha hb hc hd
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      have hspec := greedySidon_succ_spec n ih
      -- `range (n+1+1) = insert (n+1) (range (n+1))`, so the prefix image is
      -- `insert (greedySidon (n+1)) (image … range (n+1)) = image … ∪ {greedySidon (n+1)}`.
      rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq, Finset.union_comm]
      exact hspec.2

/-- The greedy Sidon sequence is strictly increasing.  (Was an axiom.) -/
theorem greedy_sidon_strict_mono : StrictMono greedySidon :=
  strictMono_nat_of_lt_succ fun n => (greedySidon_succ_spec n (greedy_sidon_is_sidon n)).1

/- ## Known Lower Bound -/

/-- **Known lower bound:** the greedy Sidon sequence grows at least as N^{1/3}.
    There exists a constant C > 0 such that |A ∩ [1,N]| ≥ C · N^{1/3} for all N ≥ 1.
    This follows from a forbidden-sum counting argument: O(k²) blocked values per step
    means the k-th element is at most O(k³), so k ≥ Ω(N^{1/3}). -/
axiom greedy_sidon_lower_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
    C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (greedySidonCount N : ℝ)

/-- **Erdős–Turán upper bound:** any Sidon set in [1,N] has at most √N + O(N^{1/4}) elements.
    So the greedy sequence satisfies f(N) ≤ √N + C·N^{1/4} for some constant C > 0. -/
axiom erdos_turan_upper_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
    (greedySidonCount N : ℝ) ≤ Real.sqrt (N : ℝ) + C * (N : ℝ) ^ ((1 : ℝ) / 4)

/- ## The Main Conjecture -/

/-- **Main conjecture (open):** The greedy Sidon sequence achieves near-optimal growth.
    For every ε > 0 there exists C_ε > 0 such that |A ∩ [1,N]| ≥ C_ε · N^{1/2 - ε}
    for all sufficiently large N. This would show greedy is nearly as good as optimal. -/
axiom greedy_sidon_growth_conjecture : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (greedySidonCount N : ℝ)

/- ## Difference Set Question -/

/-- The difference set A - A = {a(m) - a(n) : m > n}. -/
noncomputable def greedySidonDiffSet : Set ℕ :=
  { d : ℕ | ∃ m n : ℕ, m > n ∧ greedySidon m - greedySidon n = d }

/-- **Open question (Erdős–Graham):** Does the difference set A - A have positive
    upper density? There exists δ > 0 with infinitely many N satisfying
    |{d ≤ N : d ∈ A-A}| ≥ δ · N. -/
axiom greedy_sidon_diffset_pos_density : ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ N : ℕ,
    B ≤ N ∧ δ * (N : ℝ) ≤
    (Set.ncard (greedySidonDiffSet ∩ Set.Icc 1 N) : ℝ)

/- ## Connection to Random Sidon Sets -/
/- A random Sidon set in [1,N] has expected size ~N^{1/3} (birthday paradox).
   The greedy sequence empirically achieves ~N^{0.497}, far exceeding randomness. -/
