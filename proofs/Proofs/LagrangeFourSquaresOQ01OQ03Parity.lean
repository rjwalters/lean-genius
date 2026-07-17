import Proofs.LagrangeFourSquaresOQ01OQ03
import Mathlib

/-
# Parity of the four-square representation count `r₄`

`LagrangeFourSquaresOQ01OQ03` defines `r4 n` as the number of integer quadruples
`(x₁,x₂,x₃,x₄)` in the box `[-⌊√n⌋, ⌊√n⌋]⁴` with `x₁²+x₂²+x₃²+x₄² = n`, and
develops the arithmetic Jacobi right-hand side `jacobiCount n = 8·Σ_{d∣n,4∤d} d`.
The deep theorem `r4 = jacobiCount` is a genuine Mathlib gap (only pinned for
small `n` by the finite oracle).

This file records a structural fact about `r4` that is **independent of Jacobi's
formula**: for every `n ≥ 1`,

    `r4 n` is **even**.

The reason is the sign symmetry `x ↦ -x`: negating all four coordinates is a
fixed-point-free involution of the representation set (a fixed point would need
`x = -x`, i.e. `x = 0`, forcing `n = 0`), so the representations pair off and the
count is even. Since Jacobi predicts `r4 n = 8·(…)`, an even (indeed `8 ∣`) count
is expected; this file proves the elementary `2 ∣ r4 n` half directly from the
symmetry, with no arithmetic input.

The first result is a reusable combinatorial lemma — a fixed-point-free
involution of a finite set has even cardinality — proved by strong induction,
peeling off one 2-element orbit `{x, g x}` at a time.

0 sorries, 0 axioms.
-/

namespace LagrangeFourSquaresOQ01OQ03

open Finset

/-- **A fixed-point-free involution has even cardinality.** If `g` is an involution
of the ambient type that maps a finite set `s` into itself and has no fixed point on
`s`, then `s` splits into 2-element orbits `{x, g x}`, so `s.card` is even. Proved by
strong induction on `s`, removing one orbit at a time. -/
theorem even_card_of_fixedPointFree_involution {α : Type*} [DecidableEq α]
    (g : α → α) (hg : Function.Involutive g) :
    ∀ s : Finset α, (∀ x ∈ s, g x ∈ s) → (∀ x ∈ s, g x ≠ x) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hmem hfpf
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hgx : g x ∈ s := hmem x hx
      have hne : g x ≠ x := hfpf x hx
      have hpair : ({x, g x} : Finset α) ⊆ s := by
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hx
        · exact hgx
      set t := s \ {x, g x} with ht
      have htss : t ⊂ s := Finset.sdiff_ssubset hpair ⟨x, by simp⟩
      -- `t` is still closed under `g`.
      have hmemt : ∀ y ∈ t, g y ∈ t := by
        intro y hy
        rw [ht, mem_sdiff] at hy ⊢
        obtain ⟨hys, hy2⟩ := hy
        simp only [mem_insert, mem_singleton, not_or] at hy2
        refine ⟨hmem y hys, ?_⟩
        simp only [mem_insert, mem_singleton, not_or]
        refine ⟨fun h => hy2.2 ?_, fun h => hy2.1 (hg.injective h)⟩
        -- `g y = x ⟹ y = g x`
        have := congrArg g h
        rwa [hg y] at this
      have hfpft : ∀ y ∈ t, g y ≠ y := fun y hy => hfpf y (mem_sdiff.mp hy).1
      -- Cardinality drops by exactly 2.
      have hcard : s.card = t.card + 2 := by
        have hu : t ∪ ({x, g x} : Finset α) = s := Finset.sdiff_union_of_subset hpair
        have hd : Disjoint t ({x, g x} : Finset α) := by rw [ht]; exact Finset.sdiff_disjoint
        have hc := Finset.card_union_of_disjoint hd
        rw [hu, Finset.card_pair hne.symm] at hc
        omega
      rw [hcard]
      exact (ih t htss hmemt hfpft).add even_two

/-- Negation of a coordinate quadruple `(x₁,x₂,x₃,x₄) ↦ (-x₁,-x₂,-x₃,-x₄)`. -/
def negQuad (p : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (-p.1, -p.2.1, -p.2.2.1, -p.2.2.2)

theorem negQuad_involutive : Function.Involutive negQuad := by
  rintro ⟨a, b, c, d⟩
  simp only [negQuad, neg_neg]

/-- `box n` is symmetric under negation: `x ∈ box n ↔ -x ∈ box n`. -/
theorem neg_mem_box {n : ℕ} {x : ℤ} (hx : x ∈ box n) : -x ∈ box n := by
  rw [box, Finset.mem_image] at hx ⊢
  obtain ⟨i, hi, hix⟩ := hx
  rw [Finset.mem_range] at hi
  exact ⟨2 * Nat.sqrt n - i, Finset.mem_range.mpr (by omega), by omega⟩

/-- **`r₄` is even for every positive `n`.** The sign involution `negQuad` maps the
representation set to itself, and on `n ≥ 1` it is fixed-point-free (a fixed
quadruple would be all-zero, forcing `n = 0`). Hence the representations pair up
`{p, -p}` and `r4 n` is even. This is the elementary parity content of Jacobi's
`r4 n = 8·(…)` formula, obtained here from symmetry alone, independent of the
(Mathlib-blocked) exact formula. -/
theorem r4_even {n : ℕ} (hn : 1 ≤ n) : Even (r4 n) := by
  classical
  set S := (box n ×ˢ box n ×ˢ box n ×ˢ box n).filter
    (fun p => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = (n : ℤ)) with hS
  have hmem : ∀ p ∈ S, negQuad p ∈ S := by
    intro p hp
    rw [hS, mem_filter, mem_product, mem_product, mem_product] at hp ⊢
    obtain ⟨⟨h1, h2, h3, h4⟩, hsum⟩ := hp
    refine ⟨⟨neg_mem_box h1, neg_mem_box h2, neg_mem_box h3, neg_mem_box h4⟩, ?_⟩
    simpa only [negQuad, neg_sq] using hsum
  have hfpf : ∀ p ∈ S, negQuad p ≠ p := by
    rintro ⟨a, b, c, d⟩ hp hcontra
    rw [hS, mem_filter] at hp
    obtain ⟨_, hsum⟩ := hp
    simp only [negQuad, Prod.mk.injEq] at hcontra
    obtain ⟨ha, hb, hc, hd⟩ := hcontra
    have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    subst ha0 hb0 hc0 hd0
    norm_num at hsum
    omega
  have hcard : r4 n = S.card := by rw [r4, hS]
  rw [hcard]
  exact even_card_of_fixedPointFree_involution negQuad negQuad_involutive S hmem hfpf

end LagrangeFourSquaresOQ01OQ03
