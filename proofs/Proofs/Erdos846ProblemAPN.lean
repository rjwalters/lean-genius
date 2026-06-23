/-
  Erdős Problem #846 — AlphaProof Nexus port

  Source: DeepMind AlphaProof Nexus Results (2026-05-21)
  https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_846.lean
  Paper: arXiv:2605.22763v1

  This file ports the Lean 4 proof produced by AlphaProof Nexus for Erdős
  Problem #846 (Erdős–Nešetřil–Rödl, 1992): does an infinite ε-non-trilinear
  planar set decompose into finitely many non-collinear subsets? AlphaProof
  Nexus settled this **negatively**: the construction `A_set` (built from the
  Elekes parametrisation `q(i,j) = (t i + t j, t i² + t i · t j + t j²)` with
  `t_seq n = 100^(4ⁿ)`) is infinite, (1/2)-non-trilinear via a bipartite max-cut
  argument, but is NOT weakly non-trilinear via a Ramsey-for-triangles argument.

  The original used `FormalConjectures.Util.ProblemImports` and the FormalConjectures-
  specific `answer(...)` elaborator; here we replace those with `import Mathlib`
  and the identity respectively. The namespace is renamed `Erdos846APN` to avoid
  collision with the gallery module `Proofs/Erdos846Problem.lean`. The proof body
  is otherwise verbatim from the AlphaProof Nexus output, with one local
  preamble: the `ℝ²` notation and `NonTrilinear` predicate (defined in
  `FormalConjecturesForMathlib/Geometry/2d.lean` but not exported by Mathlib)
  are inlined verbatim from that file (also Apache-2.0).

  The main result is `target_theorem_0`, which asserts the conjecture is
  equivalent to `False`. The intermediate result `target_false` provides the
  refutation: `¬ (∀ A : Set ℝ², ∀ ε > 0, A.Infinite → NonTrilinearFor A ε → WeaklyNonTrilinear A)`.

  Original copyright (Apache-2.0):

  Copyright 2025 Google LLC

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Mathlib

/-! ## Inlined `ℝ²` notation and `NonTrilinear` predicate

    From `FormalConjecturesForMathlib/Geometry/2d.lean` (Apache-2.0); inlined
    verbatim because this repository depends on pure Mathlib (v4.26.0). -/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

namespace EuclideanGeometry

variable {P : Type*}

/-- A subset `A` of points is non-trilinear if no three of its points are collinear. -/
def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

end EuclideanGeometry


set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open EuclideanGeometry

namespace Erdos846APN

section Prelims

open Classical

/-- We say a subset `A` of points in the plane is `ε`-non-trilinear if any subset
`B` of `A`, contains a non-trilinear subset `C` of size at least `ε|B|`. -/
def NonTrilinearFor (A : Set ℝ²) (ε : ℝ) : Prop :=
  ∀ B : Finset ℝ², ↑B ⊆ A → ∃ C ⊆ B,
    ε * B.card ≤ C.card ∧ NonTrilinear (C : Set ℝ²)

/-- We say a subset `A` of points in the plane is weakly non-trilinear if it is
a finite union of non-trilinear sets. -/
def WeaklyNonTrilinear (A : Set ℝ²) : Prop :=
  ∃ B : Finset (Set ℝ²), A = sSup B ∧ ∀ b ∈ B, NonTrilinear b

end Prelims

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
lemma bipartite_max_cut_nat (E : Finset (ℕ × ℕ)) (hE : ∀ p ∈ E, p.1 < p.2) :
  ∃ V1 : Finset ℕ, 2 * (E.filter (fun p => (p.1 ∈ V1 ∧ p.2 ∉ V1) ∨ (p.1 ∉ V1 ∧ p.2 ∈ V1))).card ≥ E.card := by
  apply(E.finite_toSet.image (Prod.fst)).bddAbove.elim
  use E.bddAbove.elim fun and J a s=> if I:∑M ∈E,∑x ∈.powerset (.range (a+and.2+1)),ite (M.1 ∈x∧M.2 ∉x ∨M.1 ∉x∧M.2 ∈x) (1) 0<E.card then(? _)else(? _)
  · cases((E.card_eq_sum_ones)▸ E.sum_le_sum fun and(A) =>Nat.succ_le.2 (Finset.sum_pos' (by valid) ⟨{and.1},by norm_num[ (J A).2.trans, (s ⟨ _,A, rfl⟩).trans,ne_of_gt, *]⟩)).not_gt I
  by_cases h :∑s ∈E,∑α ∈.powerset (.range (a+and.2+1)),ite ( (s.fst) ∈α ∧s.snd ∉α ∨s.fst ∉α ∧s.snd ∈ α) (1) 0<E.card*2^(a+and.snd)
  · convert h.not_ge.elim (E.card_nsmul_le_sum _ _ fun and(A) =>.trans (_) (by rw [← Finset.insert_erase (Finset.mem_range_succ_iff.mpr ↑(le_add_right (s (by exists and)))), Finset.sum_powerset_insert (by apply Finset.notMem_erase)]))
    exact (.trans (by norm_num[le_add_right (s (by exists and))]) (( Finset.sum_le_sum fun R M=>Nat.pos_of_ne_zero (by grind)).trans_eq Finset.sum_add_distrib))
  · refine (by_contra fun and' =>h (E.sum_comm.trans_lt ((lt_of_mul_lt_mul_left.comp ( Finset.mul_sum _ _ _).trans_lt) ?_ (2).zero_le)))
    exact ( Finset.sum_lt_sum_of_nonempty (by bound) (fun a s=>lt_of_le_of_lt (by rw [ Finset.card_filter]) (not_le.1 (and' ⟨a,.⟩)))).trans_eq (by norm_num[mul_comm E.card,mul_assoc,pow_succ'])

lemma nontrilinear_of_no_collinear_triples (C : Finset ℝ²)
  (h : ∀ p₁ p₂ p₃ : ℝ², p₁ ∈ C → p₂ ∈ C → p₃ ∈ C → p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → ¬ Collinear ℝ ({p₁, p₂, p₃} : Set ℝ²)) :
  NonTrilinear (C : Set ℝ²) := by
  use fun and=>?_
  use fun and A B K V R L M=>h _ _ _ and B V R M L

def FormsTriangle (e₁ e₂ e₃ : ℕ × ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
  ({e₁, e₂, e₃} : Set (ℕ × ℕ)) = {(i, j), (j, k), (i, k)}

lemma bipartite_has_no_triangle (V1 : Finset ℕ) (E' : Finset (ℕ × ℕ))
  (hE' : ∀ p ∈ E', (p.1 ∈ V1 ∧ p.2 ∉ V1) ∨ (p.1 ∉ V1 ∧ p.2 ∈ V1))
  (e₁ e₂ e₃ : ℕ × ℕ) (he1 : e₁ ∈ E') (he2 : e₂ ∈ E') (he3 : e₃ ∈ E') :
  ¬ FormsTriangle e₁ e₂ e₃ := by
  change¬_ ∈ {s |_}
  push_cast[Prod.forall,not_exists,not_and,Set.ext_iff,Set.mem_setOf,Set.mem_insert_iff,Set.mem_singleton_iff]at*
  use fun and _ _ _ _ f=>absurd (f and _|>.2 (by repeat constructor)) fun and=>absurd (f _ _|>.2 (.inr (by repeat constructor)))<|absurd (f _ _|>.2 (.inr (.inr rfl))) ∘by grind

def IsGoodMap (q : ℕ × ℕ → ℝ²) : Prop :=
  (∀ e₁ e₂, e₁.1 < e₁.2 → e₂.1 < e₂.2 → e₁ ≠ e₂ → q e₁ ≠ q e₂) ∧
  ∀ e₁ e₂ e₃ : ℕ × ℕ,
    e₁.1 < e₁.2 → e₂.1 < e₂.2 → e₃.1 < e₃.2 →
    e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
    (Collinear ℝ ({q e₁, q e₂, q e₃} : Set ℝ²) ↔ FormsTriangle e₁ e₂ e₃)

lemma elekes_identity (a b c : ℝ) :
  let x1 := a + b; let y1 := a^2 + a*b + b^2
  let x2 := b + c; let y2 := b^2 + b*c + c^2
  let x3 := a + c; let y3 := a^2 + a*c + c^2
  (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1) := by
  intros
  ring

noncomputable def real_point (x y : ℝ) : ℝ² :=
  let f : Fin 2 → ℝ := ![x, y]
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm f

lemma real_point_inj (x1 y1 x2 y2 : ℝ) (h : real_point x1 y1 = real_point x2 y2) :
  x1 = x2 ∧ y1 = y2 := by
  simp_all[ Erdos846APN.real_point]

lemma collinear_iff_det2 (x1 y1 x2 y2 x3 y3 : ℝ) :
  Collinear ℝ ({real_point x1 y1, real_point x2 y2, real_point x3 y3} : Set ℝ²) ↔
  (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1) := by
  conv_lhs =>norm_num[collinear_iff_of_mem ((Set.mem_insert _ _)), Erdos846APN.real_point]
  aesop
  · simp_all[mul_comm, mul_mul_mul_comm]
    cases@isEmpty_or_nonempty ℝ
    · subsingleton
    replace h :x2=w_1*w 0+x1∧y2 =w_1*w (1)+y1∧x3=w_2*w 0+x1∧y3 =w_2*w (1) +y1
    · use congr_arg (· 0) (h),congr_arg (@ · (1)) (h),congr_arg (@. 0) (h_1),congr_arg (@ · (1)) (h_1)
    · bound
  by_contra!
  norm_num at this
  simp_all[@forall_comm ℝ²]
  obtain ⟨rfl⟩ :=eq_or_ne x2 x1
  · simp_all[sub_eq_zero]
    rcases a with@rfl|rfl
    · use this ↑(y2-y1) (.single @1 1) (eq_of_norm_sub_eq_zero (by norm_num[ EuclideanSpace.norm_eq])) ↑(y3-y1) (eq_of_norm_sub_eq_zero (by norm_num[ EuclideanSpace.norm_eq]))
    · use this 0 _ (by module) (1) (eq_add_of_sub_eq (one_smul _ _).symm)
  · apply this (1) @_ (by rw [one_smul, sub_add_cancel]) ((x3-x1)/(x2-x1))
    exact (eq_add_of_sub_eq (eq_of_norm_sub_eq_zero (by norm_num[←a,div_mul_eq_mul_div, sub_ne_zero.2 (by valid), EuclideanSpace.norm_eq])))

noncomputable def t_seq : ℕ → ℝ
| 0 => 100
| (n + 1) => (t_seq n)^4

lemma t_seq_pos (n : ℕ) : t_seq n ≥ 100 := by
  delta t_seq
  refine n.rec ↑le_rfl fun and true => true.trans (le_self_pow₀ (by ·linear_combination true) (by decide) )

lemma t_seq_int (n : ℕ) : ∃ (k : ℤ), t_seq n = (k : ℝ) := by
  delta t_seq
  induction n with |zero=>repeat constructor|succ a s=>cases↑s with use (by assumption^4),by simp_all

lemma abs_ge_one_of_int (x y : ℝ) (hx : ∃ k : ℤ, x = k) (hy : ∃ k : ℤ, y = k) (hneq : x ≠ y) : |x - y| ≥ 1 := by
  refine hy.elim (hx.elim fun and true A B => true▸B▸mod_cast abs_sub_pos.mpr (by ·bound : ¬ and = A) )

lemma t_seq_bound_linear_pos (A B T t : ℝ) (hA : A ≥ 1) (hB : |B| ≤ 22 * T^3) (hT : T ≥ 100) (ht : t ≥ T^4) :
  A * t + B > 0 := by
  linarith [neg_le_abs B, mul_le_mul_of_nonneg_right hA (ht.trans' (by positivity) ), mul_le_mul_of_nonneg_left hT ((norm_nonneg B).trans hB), (by positivity: T ^3 > 0)]

lemma t_seq_bound_linear_neg (A B T t : ℝ) (hA : A ≤ -1) (hB : |B| ≤ 22 * T^3) (hT : T ≥ 100) (ht : t ≥ T^4) :
  A * t + B < 0 := by
  linarith[le_abs_self B, mul_le_mul_of_nonneg_right (hA) (ht.trans' (by positivity) ), mul_le_mul_of_nonneg_right hT ((norm_nonneg B).trans hB), (by positivity: T ^3 > 0)]

lemma t_seq_strict_mono : StrictMono t_seq := by
  delta t_seq
  use strictMono_nat_of_lt_succ fun and=>lt_self_pow₀ (and.rec (by bound) fun and Y=>one_lt_pow₀ Y (by decide)) (by decide)

lemma t_seq_bound_A (A B C T t : ℝ) (hA : A ≥ 1) (hB : |B| ≤ 10 * T^2) (hC : |C| ≤ 22 * T^3) (hT : T ≥ 100)
  (ht : t ≥ T^4) :
  A * t^2 + B * t + C > 0 := by
  nlinarith only [ht, max_le_iff.mp hB, max_le_iff.mp hC,pow_three (T-100),pow_three (T^2-100),hA,hT]

lemma t_seq_bound_A_neg (A B C T t : ℝ) (hA : A ≤ -1) (hB : |B| ≤ 10 * T^2) (hC : |C| ≤ 22 * T^3) (hT : T ≥ 100)
  (ht : t ≥ T^4) :
  A * t^2 + B * t + C < 0 := by
  nlinarith only[ht, true,hA,pow_three (T-100 : ℝ),le_sup_left.trans hB,le_sup_left.trans hC, true,pow_three (T^2-100 : ℝ), hT]

lemma t_seq_sum_inj_of_lt (i j k l : ℕ) (h1 : i < j) (h2 : k < l) (h3 : j < l ∨ (j = l ∧ i < k)) :
  t_seq i + t_seq j < t_seq k + t_seq l := by
  delta t_seq
  let x : ℕ →ℝ:=Nat.rec 100 fun and true => true^4
  convert_to x i+x j <x k + x l
  · exact (congr_arg₂ _) @(i.rec ↑rfl fun and=>congr_arg (@. ^4)) (j.rec ↑rfl fun and=>congr_arg (@ · ^4 ) )
  · exact (congr_arg₂ _) @(k.rec ↑rfl fun and=>congr_arg (@ · ^4)) (l.rec ↑rfl fun and=>congr_arg (@ · ^4 ) )
  have A B:x B > 1:=B.rec (by(norm_num [ ↑x])) fun and β=>one_lt_pow₀ β four_ne_zero
  use h3.elim ( fun and=>lt_add_of_pos_of_le (one_pos.trans (A k)) (and.rec ((add_comm _ _).trans_le ? _) fun and true => true.trans (le_self_pow₀ (A _).le (by decide)))) (·.1▸? _)
  · nlinarith[strictMono_nat_of_lt_succ ( fun and=>lt_self_pow₀ (A and) (by decide:4 > 1)) h1, A j,pow_three (x j-1),(j.rec le_rfl fun and b=>b.trans (by bound[A and]):100≤x j)]
  · linear_combination strictMono_nat_of_lt_succ ( fun and=>lt_self_pow₀ (A and) (by decide: 1<4)) (by valid:).2

lemma t_seq_sum_inj (i j k l : ℕ) (h1 : i < j) (h2 : k < l) (h3 : (i, j) ≠ (k, l)) :
  t_seq i + t_seq j ≠ t_seq k + t_seq l := by
  rcases lt_trichotomy j l with hjl | hjl | hjl
  · have h := t_seq_sum_inj_of_lt i j k l h1 h2 (Or.inl hjl)
    linarith
  · rcases lt_trichotomy i k with hik | hik | hik
    · have h := t_seq_sum_inj_of_lt i j k l h1 h2 (Or.inr ⟨hjl, hik⟩)
      linarith
    · have h_eq : (i, j) = (k, l) := by
        ext
        · exact hik
        · exact hjl
      contradiction
    · have h := t_seq_sum_inj_of_lt k l i j h2 h1 (Or.inr ⟨hjl.symm, hik⟩)
      linarith
  · have h := t_seq_sum_inj_of_lt k l i j h2 h1 (Or.inl hjl)
    linarith

lemma t_seq_inj_sum (i j k l : ℕ) (h1 : i < j) (h2 : k < l) (h3 : (i, j) ≠ (k, l)) :
  t_seq i + t_seq j ≠ t_seq k + t_seq l ∨
  (t_seq i)^2 + t_seq i * t_seq j + (t_seq j)^2 ≠ (t_seq k)^2 + t_seq k * t_seq l + (t_seq l)^2 := by
  left
  exact t_seq_sum_inj i j k l h1 h2 h3

lemma t_seq_not_collinear_p1 (ti tj tk tl tm tn : ℝ) :
  let x1 := ti + tj; let y1 := ti^2 + ti * tj + tj^2
  let x2 := tk + tl; let y2 := tk^2 + tk * tl + tl^2
  let x3 := tm + tn; let y3 := tm^2 + tm * tn + tn^2
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) =
  (x2 - x1) * tn^2 + ((x2 - x1) * tm - (y2 - y1)) * tn + ((x2 - x1) * (tm^2 - y1) - (tm - x1) * (y2 - y1)) := by
  intros
  ring

lemma t_seq_not_collinear_p2 (tk tm tn x1 y1 : ℝ) :
  let x2 := tk + tn; let y2 := tk^2 + tk * tn + tn^2
  let x3 := tm + tn; let y3 := tm^2 + tm * tn + tn^2
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) =
  (tm - tk) * (tm + tk - x1) * tn +
  ((tk - x1) * (tm^2 - y1) - (tm - x1) * (tk^2 - y1)) := by
  intros
  ring

lemma t_seq_not_collinear_p3 (ti tk tm tn : ℝ) :
  let x1 := ti + tn; let y1 := ti^2 + ti * tn + tn^2
  let x2 := tk + tn; let y2 := tk^2 + tk * tn + tn^2
  let x3 := tm + tn; let y3 := tm^2 + tm * tn + tn^2
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) =
  (tk - ti) * (tm - ti) * (tm - tk) := by
  intros
  ring

lemma FormsTriangle_symm12 (e1 e2 e3 : ℕ × ℕ) :
  FormsTriangle e1 e2 e3 ↔ FormsTriangle e2 e1 e3 := by
  dsimp [FormsTriangle]
  constructor
  · rintro ⟨i, j, k, h1, h2, h3⟩; use i, j, k; refine ⟨h1, h2, ?_⟩
    have h_eq : ({e2, e1, e3} : Set (ℕ × ℕ)) = {e1, e2, e3} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, h3]
  · rintro ⟨i, j, k, h1, h2, h3⟩; use i, j, k; refine ⟨h1, h2, ?_⟩
    have h_eq : ({e1, e2, e3} : Set (ℕ × ℕ)) = {e2, e1, e3} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, h3]

lemma FormsTriangle_symm23 (e1 e2 e3 : ℕ × ℕ) :
  FormsTriangle e1 e2 e3 ↔ FormsTriangle e1 e3 e2 := by
  dsimp [FormsTriangle]
  constructor
  · rintro ⟨i, j, k, h1, h2, h3⟩; use i, j, k; refine ⟨h1, h2, ?_⟩
    have h_eq : ({e1, e3, e2} : Set (ℕ × ℕ)) = {e1, e2, e3} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, h3]
  · rintro ⟨i, j, k, h1, h2, h3⟩; use i, j, k; refine ⟨h1, h2, ?_⟩
    have h_eq : ({e1, e2, e3} : Set (ℕ × ℕ)) = {e1, e3, e2} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, h3]

lemma FormsTriangle_symm13 (e1 e2 e3 : ℕ × ℕ) :
  FormsTriangle e1 e2 e3 ↔ FormsTriangle e3 e2 e1 := by
  dsimp [FormsTriangle]
  constructor
  · rintro ⟨i, j, k, h1, h2, h3⟩; use i, j, k; refine ⟨h1, h2, ?_⟩
    have h_eq : ({e3, e2, e1} : Set (ℕ × ℕ)) = {e1, e2, e3} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, h3]
  · rintro ⟨i, j, k, h1, h2, h3⟩; use i, j, k; refine ⟨h1, h2, ?_⟩
    have h_eq : ({e1, e2, e3} : Set (ℕ × ℕ)) = {e3, e2, e1} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h_eq, h3]

lemma t_seq_not_collinear_case3 (i k m n : ℕ)
  (h1 : i < n) (h2 : k < n) (h3 : m < n)
  (h4 : i ≠ k) (h5 : i ≠ m) (h6 : k ≠ m) :
  let x1 := t_seq i + t_seq n; let y1 := t_seq i^2 + t_seq i * t_seq n + t_seq n^2
  let x2 := t_seq k + t_seq n; let y2 := t_seq k^2 + t_seq k * t_seq n + t_seq n^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  simp_all![ne_comm, sub_eq_zero]
  replace h1:StrictMono Erdos846APN.t_seq := ( strictMono_nat_of_lt_succ fun and=>? _)
  · use h6 ∘h1.injective.eq_iff.1 ∘mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.2 (h1.injective.ne (Ne.symm h5))) ( sub_ne_zero.2 (h1.injective.ne (Ne.symm h4)))) ∘ (by linear_combination·)
  delta t_seq
  exact (lt_self_pow₀ (and.rec (by ·norm_num) fun and x => one_lt_pow₀ ↑x (by decide) ) (by decide) )

lemma case1_sum_neq (i j k l : ℕ) (h1 : i < j) (h2 : k < l)
  (hneq : (i, j) ≠ (k, l)) :
  t_seq k + t_seq l - (t_seq i + t_seq j) ≠ 0 := by
  intro h
  have h_eq : t_seq i + t_seq j = t_seq k + t_seq l := by linarith
  have h_inj := t_seq_sum_inj i j k l h1 h2 hneq
  exact h_inj h_eq

lemma case2_sum_neq (i j k m n : ℕ) (h1 : i < j) (h2 : k < n) (h3 : m < n)
  (h4 : j < n) (h5 : k ≠ m)
  (htri : ¬ FormsTriangle (i, j) (k, n) (m, n)) :
  t_seq m + t_seq k - (t_seq i + t_seq j) ≠ 0 := by
  intro h_eq
  have h_sum : t_seq m + t_seq k = t_seq i + t_seq j := by linarith
  rcases lt_trichotomy m k with hmk | hmk | hmk
  · have h_neq : (i, j) ≠ (m, k) := by
      intro h_eq2
      have h_tri' : FormsTriangle (i, j) (k, n) (m, n) := by
        rw [h_eq2]
        exact ⟨m, k, n, hmk, h2, rfl⟩
      exact htri h_tri'
    have h_inj := t_seq_sum_inj i j m k h1 hmk h_neq
    exact h_inj h_sum.symm
  · exact h5 hmk.symm
  · have h_neq : (i, j) ≠ (k, m) := by
      intro h_eq2
      have h_tri' : FormsTriangle (i, j) (k, n) (m, n) := by
        rw [h_eq2]
        have h_set_eq : ({(k, m), (k, n), (m, n)} : Set (ℕ × ℕ)) = {(k, m), (m, n), (k, n)} := by
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        exact ⟨k, m, n, hmk, h3, h_set_eq⟩
      exact htri h_tri'
    have h_sum2 : t_seq k + t_seq m = t_seq i + t_seq j := by linarith
    have h_inj := t_seq_sum_inj i j k m h1 hmk h_neq
    exact h_inj h_sum2.symm

lemma t_seq_le_of_le (a b : ℕ) (h : a ≤ b) : t_seq a ≤ t_seq b := StrictMono.monotone t_seq_strict_mono h

lemma case1_bounds (i j k l m : ℕ) (T : ℝ)
  (hi : t_seq i ≤ T) (hj : t_seq j ≤ T)
  (hk : t_seq k ≤ T) (hl : t_seq l ≤ T) (hm : t_seq m ≤ T)
  (hpos_i : t_seq i ≥ 100) (hpos_j : t_seq j ≥ 100)
  (hpos_k : t_seq k ≥ 100) (hpos_l : t_seq l ≥ 100) (hpos_m : t_seq m ≥ 100) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq l; let y2 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let A := x2 - x1
  let B := A * t_seq m - (y2 - y1)
  let C := A * ((t_seq m)^2 - y1) - (t_seq m - x1) * (y2 - y1)
  |B| ≤ 10 * T^2 ∧ |C| ≤ 22 * T^3 := by
  classical constructor
  · use abs_le.2 (by repeat use (by nlinarith))
  have:0≤(T- Erdos846APN.t_seq k) *T∧0≤(T- Erdos846APN.t_seq l)* T∧0≤(T- Erdos846APN.t_seq m)* T∧0≤(T- Erdos846APN.t_seq i) *(T- 0) := by bound
  have:0≤(T- Erdos846APN.t_seq j) *(T-0) := by bound
  use abs_le.2 (by repeat use (by nlinarith[mul_le_mul_of_nonneg_left hpos_i (sub_nonneg.2 hj),mul_le_mul_of_nonneg_left hpos_j (sub_nonneg.2 hk),mul_le_mul_of_nonneg_left hpos_k (sub_nonneg.2 hl)]))

lemma case2_bounds (i j k m : ℕ) (T : ℝ)
  (hi : t_seq i ≤ T) (hj : t_seq j ≤ T)
  (hk : t_seq k ≤ T) (hm : t_seq m ≤ T)
  (hpos_i : t_seq i ≥ 100) (hpos_j : t_seq j ≥ 100)
  (hpos_k : t_seq k ≥ 100) (hpos_m : t_seq m ≥ 100) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let B := (t_seq k - x1) * ((t_seq m)^2 - y1) - (t_seq m - x1) * ((t_seq k)^2 - y1)
  |B| ≤ 22 * T^3 := by
  ring_nf at*
  have:0≤(T- Erdos846APN.t_seq k) *(T- Erdos846APN.t_seq i) ∧0≤(T- Erdos846APN.t_seq k) *(T- Erdos846APN.t_seq j) :=by bound
  have:0≤(T- Erdos846APN.t_seq m) *(T- Erdos846APN.t_seq k) ∧0≤(T- Erdos846APN.t_seq m) *(T- Erdos846APN.t_seq i) :=by push_cast[*, sub_nonneg, mul_nonneg, and_self]
  use abs_le.2 (by repeat use (by nlinarith[mul_le_mul_of_nonneg_left hj (sub_nonneg.2 hi),mul_le_mul_of_nonneg_left hpos_k (sub_nonneg.2 hpos_j),mul_le_mul_of_nonneg_left hpos_m (sub_nonneg.2 hpos_i)]))

lemma t_seq_not_collinear_case2 (i j k m n : ℕ)
  (h1 : i < j) (h2 : k < n) (h3 : m < n)
  (h4 : j < n)
  (h5 : k ≠ m)
  (htri : ¬ FormsTriangle (i, j) (k, n) (m, n)) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq n; let y2 := t_seq k^2 + t_seq k * t_seq n + t_seq n^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  intros x1 y1 x2 y2 x3 y3
  have h_eq : (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) =
    (t_seq m - t_seq k) * (t_seq m + t_seq k - x1) * t_seq n + ((t_seq k - x1) * ((t_seq m)^2 - y1) - (t_seq m - x1) * ((t_seq k)^2 - y1)) := by
    dsimp [x1, y1, x2, y2, x3, y3]
    ring
  let A := (t_seq m - t_seq k) * (t_seq m + t_seq k - x1)
  let B := (t_seq k - x1) * ((t_seq m)^2 - y1) - (t_seq m - x1) * ((t_seq k)^2 - y1)
  have h_poly : (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) = A * t_seq n + B := h_eq
  have hn_pos : n ≥ 1 := by omega
  let T := t_seq (n - 1)
  have hT_pos : T ≥ 100 := t_seq_pos (n - 1)
  have ht_seq : t_seq n = T^4 := by
    cases n with
    | zero => exact False.elim (by omega)
    | succ n' => rfl
  have ht_T4 : t_seq n ≥ T^4 := by linarith
  have hB : |B| ≤ 22 * T^3 := case2_bounds i j k m T (t_seq_le_of_le i (n - 1) (by omega)) (t_seq_le_of_le j (n - 1) (by omega)) (t_seq_le_of_le k (n - 1) (by omega)) (t_seq_le_of_le m (n - 1) (by omega)) (t_seq_pos i) (t_seq_pos j) (t_seq_pos k) (t_seq_pos m)
  have h_m_neq_k : t_seq m - t_seq k ≠ 0 := by
    intro h_eq2
    have h_eq3 : t_seq m = t_seq k := by linarith
    have h_eq4 : m = k := StrictMono.injective t_seq_strict_mono h_eq3
    exact h5 h_eq4.symm
  have h_sum_neq : t_seq m + t_seq k - x1 ≠ 0 := case2_sum_neq i j k m n h1 h2 h3 h4 h5 htri
  have h_A_neq : A ≠ 0 := mul_ne_zero h_m_neq_k h_sum_neq
  have hA_int : ∃ Z : ℤ, A = Z := by
    rcases t_seq_int m with ⟨Zm, hZm⟩
    rcases t_seq_int k with ⟨Zk, hZk⟩
    rcases t_seq_int i with ⟨Zi, hZi⟩
    rcases t_seq_int j with ⟨Zj, hZj⟩
    use (Zm - Zk) * (Zm + Zk - (Zi + Zj))
    dsimp [A, x1]
    push_cast
    rw [hZm, hZk, hZi, hZj]
  have h_A_ge_1 : A ≥ 1 ∨ A ≤ -1 := by
    rcases hA_int with ⟨Z, hZ⟩
    have hZ_neq : Z ≠ 0 := by
      intro h
      rw [h] at hZ
      push_cast at hZ
      exact h_A_neq hZ
    have hZ_ge : Z ≥ 1 ∨ Z ≤ -1 := by omega
    rcases hZ_ge with hZ_pos | hZ_neg
    · left; rw [hZ]; exact_mod_cast hZ_pos
    · right; rw [hZ]; exact_mod_cast hZ_neg
  rcases h_A_ge_1 with hA_pos | hA_neg
  · have h_pos := t_seq_bound_linear_pos A B T (t_seq n) hA_pos hB hT_pos ht_T4
    linarith
  · have h_neg := t_seq_bound_linear_neg A B T (t_seq n) hA_neg hB hT_pos ht_T4
    linarith

lemma t_seq_not_collinear_case1 (i j k l m n : ℕ)
  (h1 : i < j) (h2 : k < l) (h3 : m < n)
  (h4 : j < n) (h5 : l < n)
  (hneq : (i, j) ≠ (k, l)) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq l; let y2 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  intros x1 y1 x2 y2 x3 y3
  have h_eq : (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) =
    (x2 - x1) * (t_seq n)^2 + ((x2 - x1) * t_seq m - (y2 - y1)) * t_seq n + ((x2 - x1) * ((t_seq m)^2 - y1) - (t_seq m - x1) * (y2 - y1)) := by
    dsimp [x1, y1, x2, y2, x3, y3]
    ring
  let A := x2 - x1
  let B := A * t_seq m - (y2 - y1)
  let C := A * ((t_seq m)^2 - y1) - (t_seq m - x1) * (y2 - y1)
  have h_poly : (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) = A * (t_seq n)^2 + B * t_seq n + C := h_eq
  have hn_pos : n ≥ 1 := by omega
  let T := t_seq (n - 1)
  have hT_pos : T ≥ 100 := t_seq_pos (n - 1)
  have ht_seq : t_seq n = T^4 := by
    cases n with
    | zero => exact False.elim (by omega)
    | succ n' => rfl
  have ht_T4 : t_seq n ≥ T^4 := by linarith
  have h_bounds := case1_bounds i j k l m T (t_seq_le_of_le i (n - 1) (by omega)) (t_seq_le_of_le j (n - 1) (by omega)) (t_seq_le_of_le k (n - 1) (by omega)) (t_seq_le_of_le l (n - 1) (by omega)) (t_seq_le_of_le m (n - 1) (by omega)) (t_seq_pos i) (t_seq_pos j) (t_seq_pos k) (t_seq_pos l) (t_seq_pos m)
  have hB : |B| ≤ 10 * T^2 := h_bounds.1
  have hC : |C| ≤ 22 * T^3 := h_bounds.2
  have h_A_neq : A ≠ 0 := case1_sum_neq i j k l h1 h2 hneq
  have hA_int : ∃ Z : ℤ, A = Z := by
    rcases t_seq_int k with ⟨Zk, hZk⟩
    rcases t_seq_int l with ⟨Zl, hZl⟩
    rcases t_seq_int i with ⟨Zi, hZi⟩
    rcases t_seq_int j with ⟨Zj, hZj⟩
    use Zk + Zl - (Zi + Zj)
    dsimp [A, x1, x2]
    push_cast
    linarith
  have h_A_ge_1 : A ≥ 1 ∨ A ≤ -1 := by
    rcases hA_int with ⟨Z, hZ⟩
    have hZ_neq : Z ≠ 0 := by
      intro h
      rw [h] at hZ
      push_cast at hZ
      exact h_A_neq hZ
    have hZ_ge : Z ≥ 1 ∨ Z ≤ -1 := by omega
    rcases hZ_ge with hZ_pos | hZ_neg
    · left; rw [hZ]; exact_mod_cast hZ_pos
    · right; rw [hZ]; exact_mod_cast hZ_neg
  rcases h_A_ge_1 with hA_pos | hA_neg
  · have h_pos := t_seq_bound_A A B C T (t_seq n) hA_pos hB hC hT_pos ht_T4
    linarith
  · have h_neg := t_seq_bound_A_neg A B C T (t_seq n) hA_neg hB hC hT_pos ht_T4
    linarith

lemma t_seq_not_collinear_symm12 (i j k l m n : ℕ)
  (h1 : i < j) (h2 : k < l) (h3 : m < n)
  (h4 : (i, j) ≠ (k, l)) (h5 : (i, j) ≠ (m, n)) (h6 : (k, l) ≠ (m, n))
  (htri : ¬ FormsTriangle (i, j) (k, l) (m, n)) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq l; let y2 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) ↔
  let x1 := t_seq k + t_seq l; let y1 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let x2 := t_seq i + t_seq j; let y2 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  apply not_congr ∘.symm ∘.trans (by rw [←neg_mul_neg _,neg_sub])
  repeat use(by linear_combination·.symm)

lemma t_seq_not_collinear_symm23 (i j k l m n : ℕ)
  (h1 : i < j) (h2 : k < l) (h3 : m < n)
  (h4 : (i, j) ≠ (k, l)) (h5 : (i, j) ≠ (m, n)) (h6 : (k, l) ≠ (m, n))
  (htri : ¬ FormsTriangle (i, j) (k, l) (m, n)) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq l; let y2 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) ↔
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq m + t_seq n; let y2 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  let x3 := t_seq k + t_seq l; let y3 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  constructor
  · use@.symm
  · use .symm

lemma t_seq_not_collinear_n_max (i j k l m n : ℕ)
  (h1 : i < j) (h2 : k < l) (h3 : m < n)
  (hmax_j : j ≤ n) (hmax_l : l ≤ n)
  (h4 : (i, j) ≠ (k, l)) (h5 : (i, j) ≠ (m, n)) (h6 : (k, l) ≠ (m, n))
  (htri : ¬ FormsTriangle (i, j) (k, l) (m, n)) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq l; let y2 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  intros x1 y1 x2 y2 x3 y3
  rcases lt_trichotomy j n with hjn | hjn | hjn
  · rcases lt_trichotomy l n with hln | hln | hln
    · exact t_seq_not_collinear_case1 i j k l m n h1 h2 h3 hjn hln h4
    · have hln_eq : l = n := by linarith
      have h_k_neq_m : k ≠ m := by
        intro h_km
        have h_eq : (k, l) = (m, n) := by rw [h_km, hln_eq]
        exact h6 h_eq
      have htri' : ¬ FormsTriangle (i, j) (k, n) (m, n) := by
        intro h_tri2
        have h_tri3 : FormsTriangle (i, j) (k, l) (m, n) := by
          have hh : (k, n) = (k, l) := by rw [← hln_eq]
          rw [hh] at h_tri2
          exact h_tri2
        exact htri h_tri3
      have h_not := t_seq_not_collinear_case2 i j k m n h1 (by linarith) h3 hjn h_k_neq_m htri'
      have h_eq_l : t_seq n = t_seq l := by rw [hln_eq]
      dsimp [x1, y1, x2, y2, x3, y3]
      rw [← h_eq_l]
      exact h_not
    · exact False.elim (by linarith)
  · rcases lt_trichotomy l n with hln | hln | hln
    · have hjn_eq : j = n := by linarith
      have h_tri' : ¬ FormsTriangle (k, l) (i, n) (m, n) := by
        intro h_tri2
        have h_tri3 := (FormsTriangle_symm12 (k, l) (i, n) (m, n)).mp h_tri2
        have hh : (i, n) = (i, j) := by rw [hjn_eq]
        rw [hh] at h_tri3
        exact htri h_tri3
      have h_i_neq_m : i ≠ m := by
        intro h_im
        have h_eq : (i, j) = (m, n) := by rw [h_im, hjn_eq]
        exact h5 h_eq
      have h_not := t_seq_not_collinear_case2 k l i m n h2 (by linarith) h3 hln h_i_neq_m h_tri'
      have h_eq1 : t_seq n = t_seq j := by rw [hjn_eq]
      have h_symm := t_seq_not_collinear_symm12 i j k l m n h1 h2 h3 h4 h5 h6 htri
      have h_not2 : (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
        apply h_symm.mpr
        dsimp
        have h_eq1' : t_seq j = t_seq n := by rw [hjn_eq]
        rw [h_eq1']
        exact h_not
      exact h_not2
    · have hjn_eq : j = n := by linarith
      have hln_eq : l = n := by linarith
      have h_i_neq_k : i ≠ k := by
        intro h_ik
        have h_eq : (i, j) = (k, l) := by rw [h_ik, hjn_eq, hln_eq]
        exact h4 h_eq
      have h_i_neq_m : i ≠ m := by
        intro h_im
        have h_eq : (i, j) = (m, n) := by rw [h_im, hjn_eq]
        exact h5 h_eq
      have h_k_neq_m : k ≠ m := by
        intro h_km
        have h_eq : (k, l) = (m, n) := by rw [h_km, hln_eq]
        exact h6 h_eq
      have h_not := t_seq_not_collinear_case3 i k m n (by linarith) (by linarith) h3 h_i_neq_k h_i_neq_m h_k_neq_m
      have h_eq1 : t_seq j = t_seq n := by rw [hjn_eq]
      have h_eq2 : t_seq l = t_seq n := by rw [hln_eq]
      have h_not2 : (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
        dsimp [x1, y1, x2, y2, x3, y3]
        rw [h_eq1, h_eq2]
        exact h_not
      exact h_not2
    · exact False.elim (by linarith)
  · exact False.elim (by linarith)

lemma t_seq_not_collinear (i j k l m n : ℕ)
  (h1 : i < j) (h2 : k < l) (h3 : m < n)
  (h4 : (i, j) ≠ (k, l)) (h5 : (i, j) ≠ (m, n)) (h6 : (k, l) ≠ (m, n))
  (htri : ¬ FormsTriangle (i, j) (k, l) (m, n)) :
  let x1 := t_seq i + t_seq j; let y1 := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
  let x2 := t_seq k + t_seq l; let y2 := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
  let x3 := t_seq m + t_seq n; let y3 := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
  (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) := by
  intros x1 y1 x2 y2 x3 y3
  have h_cases : (j ≤ n ∧ l ≤ n) ∨ (n ≤ l ∧ j ≤ l) ∨ (n ≤ j ∧ l ≤ j) := by omega
  rcases h_cases with ⟨hjn, hln⟩ | ⟨hnl, hjl⟩ | ⟨hnj, hlj⟩
  · exact t_seq_not_collinear_n_max i j k l m n h1 h2 h3 hjn hln h4 h5 h6 htri
  · have h_tri' : ¬ FormsTriangle (i, j) (m, n) (k, l) := by
      intro h_tri2
      have h_tri3 := (FormsTriangle_symm23 (i, j) (k, l) (m, n)).mpr h_tri2
      exact htri h_tri3
    have h_not := t_seq_not_collinear_n_max i j m n k l h1 h3 h2 hjl hnl h5 h4 h6.symm h_tri'
    have h_symm := t_seq_not_collinear_symm23 i j k l m n h1 h2 h3 h4 h5 h6 htri
    exact h_symm.mpr h_not
  · have h_tri' : ¬ FormsTriangle (m, n) (k, l) (i, j) := by
      intro h_tri2
      have h_tri3 := (FormsTriangle_symm13 (i, j) (k, l) (m, n)).mpr h_tri2
      exact htri h_tri3
    have h_symm13 : (x2 - x1) * (y3 - y1) ≠ (x3 - x1) * (y2 - y1) ↔
      let x1' := t_seq m + t_seq n; let y1' := t_seq m^2 + t_seq m * t_seq n + t_seq n^2
      let x2' := t_seq k + t_seq l; let y2' := t_seq k^2 + t_seq k * t_seq l + t_seq l^2
      let x3' := t_seq i + t_seq j; let y3' := t_seq i^2 + t_seq i * t_seq j + t_seq j^2
      (x2' - x1') * (y3' - y1') ≠ (x3' - x1') * (y2' - y1') := by
      dsimp only
      have h_eq : (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) =
        - ( ((t_seq k + t_seq l) - (t_seq m + t_seq n)) * ((t_seq i^2 + t_seq i * t_seq j + t_seq j^2) - (t_seq m^2 + t_seq m * t_seq n + t_seq n^2)) -
            ((t_seq i + t_seq j) - (t_seq m + t_seq n)) * ((t_seq k^2 + t_seq k * t_seq l + t_seq l^2) - (t_seq m^2 + t_seq m * t_seq n + t_seq n^2)) ) := by
        dsimp [x1, y1, x2, y2, x3, y3]
        ring
      constructor
      · intro h_neq h_eq2
        have h0 : (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1) = 0 := by linarith
        have h00 : (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1) := by linarith
        exact h_neq h00
      · intro h_neq h_eq2
        have h0 : ((t_seq k + t_seq l) - (t_seq m + t_seq n)) * ((t_seq i^2 + t_seq i * t_seq j + t_seq j^2) - (t_seq m^2 + t_seq m * t_seq n + t_seq n^2)) - ((t_seq i + t_seq j) - (t_seq m + t_seq n)) * ((t_seq k^2 + t_seq k * t_seq l + t_seq l^2) - (t_seq m^2 + t_seq m * t_seq n + t_seq n^2)) = 0 := by linarith
        have h00 : ((t_seq k + t_seq l) - (t_seq m + t_seq n)) * ((t_seq i^2 + t_seq i * t_seq j + t_seq j^2) - (t_seq m^2 + t_seq m * t_seq n + t_seq n^2)) = ((t_seq i + t_seq j) - (t_seq m + t_seq n)) * ((t_seq k^2 + t_seq k * t_seq l + t_seq l^2) - (t_seq m^2 + t_seq m * t_seq n + t_seq n^2)) := by linarith
        exact h_neq h00
    have h_not := t_seq_not_collinear_n_max m n k l i j h3 h2 h1 hnj hlj h6.symm h5.symm h4.symm h_tri'
    exact h_symm13.mpr h_not

lemma triangle_is_collinear (t : ℕ → ℝ) (i j k l m n : ℕ)
  (htri : FormsTriangle (i, j) (k, l) (m, n)) :
  let x1 := t i + t j; let y1 := t i^2 + t i * t j + t j^2
  let x2 := t k + t l; let y2 := t k^2 + t k * t l + t l^2
  let x3 := t m + t n; let y3 := t m^2 + t m * t n + t n^2
  (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1) := by
  change@_ ∈{s |_} at htri
  push_cast[Set.mem_setOf, add_assoc,Prod.forall,Prod.ext_iff,exists_and_left,Set.ext_iff,Set.mem_insert_iff,Set.mem_singleton_iff]at*
  refine htri.elim fun and ⟨a, L, T, M, E⟩=>by_contra fun and' =>absurd.comp (E _ _).2 (by repeat constructor) fun and' =>absurd.comp (E _ _).2 (.inr (by repeat constructor)) (absurd.comp (E _ _).2 (.inr<|.inr ⟨rfl, rfl⟩) ∘? _)
  grind

lemma exists_good_t : ∃ t : ℕ → ℝ,
  StrictMono t ∧
  (∀ i j k l, i < j → k < l → (i, j) ≠ (k, l) →
  (t i + t j ≠ t k + t l ∨ t i^2 + t i * t j + t j^2 ≠ t k^2 + t k * t l + t l^2)) ∧
  (∀ i j k l m n, i < j → k < l → m < n →
  (i, j) ≠ (k, l) → (i, j) ≠ (m, n) → (k, l) ≠ (m, n) →
  let x1 := t i + t j; let y1 := t i^2 + t i * t j + t j^2
  let x2 := t k + t l; let y2 := t k^2 + t k * t l + t l^2
  let x3 := t m + t n; let y3 := t m^2 + t m * t n + t n^2
  ((x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1) ↔ FormsTriangle (i, j) (k, l) (m, n))) := by
  use t_seq
  refine ⟨t_seq_strict_mono, ?_, ?_⟩
  · intro i j k l h1 h2 h3
    exact t_seq_inj_sum i j k l h1 h2 h3
  · intro i j k l m n h1 h2 h3 h4 h5 h6
    constructor
    · intro hcol
      by_contra htri
      have hnot := t_seq_not_collinear i j k l m n h1 h2 h3 h4 h5 h6 htri
      exact hnot hcol
    · intro htri
      exact triangle_is_collinear t_seq i j k l m n htri

lemma exists_good_map : ∃ q : ℕ × ℕ → ℝ², IsGoodMap q := by
  have ht := exists_good_t
  rcases ht with ⟨t, h_mono, h_inj_cond, h_col_cond⟩
  let q : ℕ × ℕ → ℝ² := fun p => real_point (t p.1 + t p.2) (t p.1^2 + t p.1 * t p.2 + t p.2^2)
  use q
  constructor
  · intro e1 e2 h1 h2 h_neq
    have h_diff := h_inj_cond e1.1 e1.2 e2.1 e2.2 h1 h2 h_neq
    intro h_eq
    have h_inj := real_point_inj _ _ _ _ h_eq
    rcases h_inj with ⟨hx, hy⟩
    cases h_diff with
    | inl hx_diff => exact hx_diff hx
    | inr hy_diff => exact hy_diff hy
  · intro e1 e2 e3 h1 h2 h3 h12 h13 h23
    have h_iff := h_col_cond e1.1 e1.2 e2.1 e2.2 e3.1 e3.2 h1 h2 h3 h12 h13 h23
    have h_col := collinear_iff_det2 (t e1.1 + t e1.2) (t e1.1^2 + t e1.1 * t e1.2 + t e1.2^2)
      (t e2.1 + t e2.2) (t e2.1^2 + t e2.1 * t e2.2 + t e2.2^2)
      (t e3.1 + t e3.2) (t e3.1^2 + t e3.1 * t e3.2 + t e3.2^2)
    rw [h_col]
    exact h_iff

def A_set (q : ℕ × ℕ → ℝ²) : Set ℝ² :=
  { p | ∃ i j : ℕ, i < j ∧ p = q (i, j) }

lemma A_set_infinite (q : ℕ × ℕ → ℝ²) (hq : IsGoodMap q) : (A_set q).Infinite := by
  delta IsGoodMap and A_set at*
  exact (Set.infinite_of_injective_forall_mem fun and R M=>congr_arg Prod.fst (by_contra (@hq.left _ _ (by constructor) (by constructor) · M))) (⟨·, _,by constructor, rfl⟩)

lemma A_set_nontrilinear (q : ℕ × ℕ → ℝ²) (hq : IsGoodMap q) : NonTrilinearFor (A_set q) (1/2) := by
  intro B hB
  have h_inj : ∀ e₁ e₂, e₁.1 < e₁.2 → e₂.1 < e₂.2 → q e₁ = q e₂ → e₁ = e₂ := by
    intro e₁ e₂ h1 h2 heq
    by_contra h_neq
    have h_diff := hq.1 e₁ e₂ h1 h2 h_neq
    exact h_diff heq
  have hE_exists : ∃ E : Finset (ℕ × ℕ), (∀ e ∈ E, e.1 < e.2) ∧ E.image q = B ∧ E.card = B.card := by
    choose! I R L using(id) hB
    classical ·refine ⟨ _,B.forall_mem_image.mpr fun and α=>(L α).1, B.image_image.trans ( (B.image_congr fun and β=>(L β).2).symm.trans B.image_id), B.card_image_of_injOn fun and R M a s=>(L R).2▸s▸(L (@ a)).right.symm⟩
  rcases hE_exists with ⟨E, hE_valid, hE_image, hE_card⟩
  have h_cut := bipartite_max_cut_nat E hE_valid
  rcases h_cut with ⟨V1, hV1⟩
  let E' := E.filter (fun p => (p.1 ∈ V1 ∧ p.2 ∉ V1) ∨ (p.1 ∉ V1 ∧ p.2 ∈ V1))
  have hE'_sub : E' ⊆ E := Finset.filter_subset _ _
  let C := E'.image q
  use C
  have hC_sub : C ⊆ B := by
    rw [← hE_image]
    exact Finset.image_subset_image hE'_sub
  refine ⟨hC_sub, ?_, ?_⟩
  · have hC_card : (C.card : ℝ) = (E'.card : ℝ) := by
      have h1 : C.card = E'.card := by
        apply Finset.card_image_of_injOn
        intro e₁ he1 e₂ he2 heq
        exact h_inj e₁ e₂ (hE_valid e₁ (hE'_sub he1)) (hE_valid e₂ (hE'_sub he2)) heq
      rw [h1]
    have hB_card_eq : (B.card : ℝ) = (E.card : ℝ) := by rw [hE_card]
    have hV1_real : (E.card : ℝ) ≤ 2 * (E'.card : ℝ) := by exact_mod_cast hV1
    rw [hC_card, hB_card_eq]
    linarith
  · apply nontrilinear_of_no_collinear_triples
    intro p₁ p₂ p₃ hp1 hp2 hp3 hneq12 hneq13 hneq23 hcol
    have he1_ex : ∃ e₁ ∈ E', q e₁ = p₁ := Finset.mem_image.mp hp1
    have he2_ex : ∃ e₂ ∈ E', q e₂ = p₂ := Finset.mem_image.mp hp2
    have he3_ex : ∃ e₃ ∈ E', q e₃ = p₃ := Finset.mem_image.mp hp3
    rcases he1_ex with ⟨e₁, he1, hq1⟩
    rcases he2_ex with ⟨e₂, he2, hq2⟩
    rcases he3_ex with ⟨e₃, he3, hq3⟩
    have he1_neq2 : e₁ ≠ e₂ := by intro h; rw [h] at hq1; exact hneq12 (hq1.symm.trans hq2)
    have he1_neq3 : e₁ ≠ e₃ := by intro h; rw [h] at hq1; exact hneq13 (hq1.symm.trans hq3)
    have he2_neq3 : e₂ ≠ e₃ := by intro h; rw [h] at hq2; exact hneq23 (hq2.symm.trans hq3)
    have he1_valid := hE_valid e₁ (hE'_sub he1)
    have he2_valid := hE_valid e₂ (hE'_sub he2)
    have he3_valid := hE_valid e₃ (hE'_sub he3)
    have hcol' : Collinear ℝ ({q e₁, q e₂, q e₃} : Set ℝ²) := by
      rw [hq1, hq2, hq3]
      exact hcol
    have h_tri := (hq.2 e₁ e₂ e₃ he1_valid he2_valid he3_valid he1_neq2 he1_neq3 he2_neq3).mp hcol'
    have hE'_bip : ∀ p ∈ E', (p.1 ∈ V1 ∧ p.2 ∉ V1) ∨ (p.1 ∉ V1 ∧ p.2 ∈ V1) := by
      intro p hp
      have hp_in := Finset.mem_filter.mp hp
      exact hp_in.2
    have h_not_tri := bipartite_has_no_triangle V1 E' hE'_bip e₁ e₂ e₃ he1 he2 he3
    exact h_not_tri h_tri

lemma weakly_nontrilinear_coloring {A : Set ℝ²} (h : WeaklyNonTrilinear A) :
  ∃ (N : ℕ) (c : ℝ² → ℕ), (∀ p ∈ A, c p < N) ∧
    (∀ p₁ p₂ p₃ : ℝ², p₁ ∈ A → p₂ ∈ A → p₃ ∈ A →
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      c p₁ = c p₂ → c p₂ = c p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set ℝ²)) := by
  rcases h with ⟨B, hB1, hB2⟩
  let B_list := B.toList
  let N := B_list.length
  let c (p : ℝ²) : ℕ := B_list.findIdx (fun s => p ∈ s)
  use N, c
  constructor
  · intro p hp
    have h_in : ∃ s ∈ B, p ∈ s := by bound
    rcases h_in with ⟨s, hs, hp_s⟩
    have h_find : List.findIdx (fun s => p ∈ s) B_list < B_list.length := by use B_list.findIdx_lt_length.mpr ⟨s, by aesop⟩
    exact h_find
  · intro p₁ p₂ p₃ hp1 hp2 hp3 hneq12 hneq13 hneq23 heq1 heq2
    have h_eq : c p₁ = c p₃ := by valid
    have h_lt : c p₁ < N := by exact B_list.findIdx_lt_length.2.comp ( hB1▸hp1).imp (by norm_num[c, B_list, N])
    have h_get : ∃ s, B_list.get ⟨c p₁, h_lt⟩ = s ∧ p₁ ∈ s ∧ p₂ ∈ s ∧ p₃ ∈ s := by norm_num[c,List.findIdx_eq] at heq1⊢
                                                                                   grind[List.findIdx_eq]
    rcases h_get with ⟨s, hs_eq, hp1s, hp2s, hp3s⟩
    have hsB : s ∈ B := by norm_num [←hs_eq, B_list, true,<-B.mem_toList]
    have h_nontri : NonTrilinear s := hB2 s hsB
    have h_sub : ({p₁, p₂, p₃} : Set ℝ²) ⊆ s := by push_cast [ *, and_self, true,Set.insert_subset_iff,Set.singleton_subset_iff]
    have h_not_col_s : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set ℝ²) := by change∀a_, _ at h_nontri
                                                                   norm_num[ *]
    exact h_not_col_s

lemma ramsey_sequence (c : ℕ × ℕ → ℕ) (N : ℕ) (hc : ∀ e, c e < N) :
  ∃ (v : ℕ → ℕ) (C : ℕ → ℕ),
    StrictMono v ∧
    (∀ i j, i < j → c (v i, v j) = C i) := by
  have R M := (Set.finite_lt_nat _).exists_lt_map_eq_of_forall_mem fun and=>hc (M, and)
  choose _ _ _ _ using(id) R
  apply (isCompact_pi_infinite fun and=>isCompact_Icc).tendsto_subseq (fun A B=>⟨zero_le _,le_of_lt (hc (B, A))⟩) |>.elim
  simp_all(config := {singlePass :=1}) -contextual [tendsto_pi_nhds]
  refine fun and A B R M=> (Classical.axiomOfChoice M).elim @fun a s=>((isCompact_Icc.isSeqCompact fun and' =>⟨zero_le _,A (B (and'.recOn 0 fun and k=>a (B k)+ (k + 1)))⟩).elim) ?_
  norm_num
  use fun and K V M W E=>⟨ fun and=>B ((V (W+and)).rec 0 fun and n=>a (B n)+ (n + 1)), R.comp (strictMono_nat_of_lt_succ (by (fin_omega))|>.comp (M.comp fun and=>by valid)), fun and' =>and,?_⟩
  refine fun and R L=>E @_ ↑le_self_add▸s _ _ ((monotone_nat_of_le_succ (by (fin_omega) ) (M (by valid) )).trans' le_self_add)

lemma pidgeonhole_3 (C : ℕ → ℕ) (N : ℕ) (hC : ∀ i, C i < N) :
  ∃ i₁ i₂ i₃, i₁ < i₂ ∧ i₂ < i₃ ∧ C i₁ = C i₂ ∧ C i₂ = C i₃ := by
  norm_num
  apply((Set.finite_lt_nat _).isCompact.isSeqCompact hC).elim
  norm_num(config := {singlePass:=1})
  use fun and n⟨x,A, B⟩=>B.exists_forall_of_atTop.elim fun and p=>⟨ _,_, A and.lt_succ_self,_, A (by constructor),by repeat use(p _ (by repeat constructor)).trans ( (p _) (by repeat constructor)).symm⟩

lemma ramsey_for_triangles (c : ℕ × ℕ → ℕ) (N : ℕ) (hc : ∀ e, c e < N) :
  ∃ i j k : ℕ, i < j ∧ j < k ∧ c (i, j) = c (j, k) ∧ c (j, k) = c (i, k) := by
  have h_seq := ramsey_sequence c N hc
  rcases h_seq with ⟨v, C, h_v_mono, h_C_eq⟩
  have hC_bound : ∀ i, C i < N := by
    intro i
    have h_lt : i < i + 1 := by omega
    have h_eq := h_C_eq i (i + 1) h_lt
    rw [← h_eq]
    exact hc (v i, v (i + 1))
  have h_ph := pidgeonhole_3 C N hC_bound
  rcases h_ph with ⟨i₁, i₂, i₃, h12, h23, hC12, hC23⟩
  use v i₁, v i₂, v i₃
  have h_v12 : v i₁ < v i₂ := h_v_mono h12
  have h_v23 : v i₂ < v i₃ := h_v_mono h23
  have h_v13 : v i₁ < v i₃ := h_v_mono (lt_trans h12 h23)
  refine ⟨h_v12, h_v23, ?_, ?_⟩
  · have hc12 := h_C_eq i₁ i₂ h12
    have hc23 := h_C_eq i₂ i₃ h23
    rw [hc12, hc23]
    exact hC12
  · have hc23 := h_C_eq i₂ i₃ h23
    have hc13 := h_C_eq i₁ i₃ (lt_trans h12 h23)
    rw [hc23, hc13]
    exact hC12.symm

lemma A_set_not_weakly (q : ℕ × ℕ → ℝ²) (hq : IsGoodMap q) : ¬ WeaklyNonTrilinear (A_set q) := by
  intro h_weak
  have h_col := weakly_nontrilinear_coloring h_weak
  rcases h_col with ⟨N, c, hc_bound, hc_nocol⟩
  let c_edge (e : ℕ × ℕ) : ℕ := if h : e.1 < e.2 then c (q e) else 0
  have h_c_edge_bound : ∀ e, c_edge e < N + 1 := by
    intro e
    dsimp [c_edge]
    split_ifs with h
    · have h_in : q e ∈ A_set q := ⟨e.1, e.2, h, rfl⟩
      have h_lt := hc_bound (q e) h_in
      omega
    · omega
  have h_ramsey := ramsey_for_triangles c_edge (N + 1) h_c_edge_bound
  rcases h_ramsey with ⟨i, j, k, hij, hjk, hc1, hc2⟩
  have hik : i < k := by omega
  have h_in1 : q (i, j) ∈ A_set q := ⟨i, j, hij, rfl⟩
  have h_in2 : q (j, k) ∈ A_set q := ⟨j, k, hjk, rfl⟩
  have h_in3 : q (i, k) ∈ A_set q := ⟨i, k, hik, rfl⟩
  have h_eq1 : c (q (i, j)) = c (q (j, k)) := by
    have h1 : c_edge (i, j) = c (q (i, j)) := dif_pos hij
    have h2 : c_edge (j, k) = c (q (j, k)) := dif_pos hjk
    omega
  have h_eq2 : c (q (j, k)) = c (q (i, k)) := by
    have h2 : c_edge (j, k) = c (q (j, k)) := dif_pos hjk
    have h3 : c_edge (i, k) = c (q (i, k)) := dif_pos hik
    omega
  have h_neq12 : q (i, j) ≠ q (j, k) := by
    apply hq.1 (i, j) (j, k) hij hjk
    intro h; cases h; omega
  have h_neq13 : q (i, j) ≠ q (i, k) := by
    apply hq.1 (i, j) (i, k) hij hik
    intro h; cases h; omega
  have h_neq23 : q (j, k) ≠ q (i, k) := by
    apply hq.1 (j, k) (i, k) hjk hik
    intro h; cases h; omega
  have h_not_col := hc_nocol (q (i, j)) (q (j, k)) (q (i, k)) h_in1 h_in2 h_in3 h_neq12 h_neq13 h_neq23 h_eq1 h_eq2
  have h_col : Collinear ℝ ({q (i, j), q (j, k), q (i, k)} : Set ℝ²) := by
    have ht : FormsTriangle (i, j) (j, k) (i, k) := by
      exact ⟨i, j, k, hij, hjk, rfl⟩
    have h_iff := hq.2 (i, j) (j, k) (i, k) hij hjk hik
    have h_diff1 : (i, j) ≠ (j, k) := by intro h; cases h; omega
    have h_diff2 : (i, j) ≠ (i, k) := by intro h; cases h; omega
    have h_diff3 : (j, k) ≠ (i, k) := by intro h; cases h; omega
    exact (h_iff h_diff1 h_diff2 h_diff3).mpr ht
  exact h_not_col h_col

lemma target_false : ¬ (∀ (A : Set ℝ²), ∀ ε > 0, A.Infinite → NonTrilinearFor A ε → WeaklyNonTrilinear A) := by
  intro h
  have h_map := exists_good_map
  rcases h_map with ⟨q, hq⟩
  have h_inf := A_set_infinite q hq
  have h_nontri := A_set_nontrilinear q hq
  have h_weak := h (A_set q) (1/2) (by norm_num) h_inf h_nontri
  have h_not_weak := A_set_not_weakly q hq
  exact h_not_weak h_weak
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : False ↔ ∀ (A : Set ℝ²) (ε : ℝ), ε > 0 → A.Infinite → NonTrilinearFor A ε → WeaklyNonTrilinear A := by
  -- EVOLVE-BLOCK-START
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    have hf := target_false
    contradiction
  -- EVOLVE-BLOCK-END

end Erdos846APN
