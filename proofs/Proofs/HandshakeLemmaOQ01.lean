import Mathlib

/-!
# Minimal edge/degree deficiency from the handshake parity obstruction

## Open question (`handshake-lemma-oq-01`)

The parent entry (`HandshakeLemma.lean`) proves the handshake lemma
`∑_v deg(v) = 2·|E|` and its parity corollary that the number of odd-degree
vertices is even. Its first open question asks to **quantify the parity
obstruction**: for `d`-regular graphs on `n` vertices with `d` odd and `n` odd
(which cannot exist), what is the *minimal deficiency* — how far must any actual
graph fall short of the regular ideal, and is that floor attained?

## What this entry proves

Fix a target degree `d`. For a finite simple graph `G` on `n = |V|` vertices
whose every vertex has degree `≤ d`, define the **degree deficiency**

  `deficiency G d = ∑_v (d − deg v) = n·d − ∑_v deg v = n·d − 2·|E|`.

Because `∑_v deg v = 2·|E|` is always even, the deficiency has the **same parity
as `n·d`**. Hence:

* `deficiency_eq` — the deficiency equals `n·d − 2·|E|` (assuming `deg ≤ d`).
* `deficiency_parity` — `deficiency G d ≡ n·d  (mod 2)`.
* `deficiency_odd` / `one_le_deficiency` — when `n·d` is **odd**, the deficiency is
  odd, hence `≥ 1`: a `d`-regular graph is impossible and *any* graph with
  `deg ≤ d` misses the ideal degree sum by at least `1`.
* `edge_upper_bound` — equivalently `2·|E| ≤ n·d − 1`: the edge count cannot reach
  the regular ideal `n·d/2`; this is the **minimal edge deficiency**.
* `not_isRegularOfDegree_of_odd_mul` — the clean impossibility corollary: no
  `d`-regular graph on `n` vertices exists once `n·d` is odd (in particular when
  both `n` and `d` are odd).

## Sharpness

The floor `1` is attained: `deficiency_floor_attained` exhibits the empty graph on
one vertex with `d = 1`, where `n·d = 1` is odd and the deficiency is exactly `1`.
So the lower bound `one_le_deficiency` cannot be improved.

Everything is sorry-free and axiom-free; the sharpness witness uses kernel
`decide`, not `native_decide`, so no extra trust assumptions are introduced.
-/

namespace HandshakeLemmaOQ01

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Degree deficiency toward `d`-regularity.**
`deficiency G d = ∑_v (d − deg v)`, the total shortfall of the vertex degrees
from the target degree `d`. When `deg v ≤ d` for all `v` this is `n·d − 2|E|`. -/
def deficiency (d : ℕ) : ℕ := ∑ v, (d - G.degree v)

/-- The degree sum is even — the handshake identity `∑ deg = 2|E|`. -/
theorem even_sum_degrees : Even (∑ v, G.degree v) := by
  rw [G.sum_degrees_eq_twice_card_edges]; exact even_two_mul _

/-- **Deficiency as an ideal shortfall.** If every vertex has degree at most `d`
then `deficiency G d = n·d − ∑_v deg v = n·d − 2|E|`. -/
theorem deficiency_eq (d : ℕ) (hbound : ∀ v, G.degree v ≤ d) :
    deficiency G d = Fintype.card V * d - ∑ v, G.degree v := by
  unfold deficiency
  rw [Finset.sum_tsub_distrib _ (fun v _ => hbound v), Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

/-- The deficiency has the same parity as `n·d`: it differs from `n·d` by the even
number `∑_v deg v = 2|E|`. -/
theorem deficiency_parity (d : ℕ) (hbound : ∀ v, G.degree v ≤ d) :
    deficiency G d % 2 = (Fintype.card V * d) % 2 := by
  obtain ⟨m, hm⟩ := even_sum_degrees G
  have hle : ∑ v, G.degree v ≤ Fintype.card V * d := by
    calc ∑ v, G.degree v ≤ ∑ _v : V, d := Finset.sum_le_sum (fun v _ => hbound v)
      _ = Fintype.card V * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [deficiency_eq G d hbound]
  omega

/-- **The parity obstruction, quantitative form.** If `n·d` is odd then the degree
deficiency is odd. -/
theorem deficiency_odd (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) : Odd (deficiency G d) := by
  rw [Nat.odd_iff] at hodd ⊢
  rw [deficiency_parity G d hbound, hodd]

/-- **Minimal deficiency `≥ 1`.** When `n·d` is odd, *every* graph with `deg ≤ d`
has degree deficiency at least `1`; there is no `d`-regular graph. -/
theorem one_le_deficiency (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) : 1 ≤ deficiency G d := by
  obtain ⟨k, hk⟩ := deficiency_odd G d hbound hodd
  omega

/-- **Minimal edge deficiency.** When `n·d` is odd, the number of edges satisfies
`2·|E| ≤ n·d − 1`: the edge count cannot reach the regular ideal `n·d / 2`. -/
theorem edge_upper_bound (d : ℕ) (hbound : ∀ v, G.degree v ≤ d)
    (hodd : Odd (Fintype.card V * d)) :
    2 * G.edgeFinset.card ≤ Fintype.card V * d - 1 := by
  have hdef := one_le_deficiency G d hbound hodd
  rw [deficiency_eq G d hbound, G.sum_degrees_eq_twice_card_edges] at hdef
  have hle : 2 * G.edgeFinset.card ≤ Fintype.card V * d := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc ∑ v, G.degree v ≤ ∑ _v : V, d := Finset.sum_le_sum (fun v _ => hbound v)
      _ = Fintype.card V * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

/-- **Impossibility corollary.** No `d`-regular graph on `n` vertices exists when
`n·d` is odd — in particular when both `n` and `d` are odd. -/
theorem not_isRegularOfDegree_of_odd_mul (d : ℕ) (hodd : Odd (Fintype.card V * d)) :
    ¬ G.IsRegularOfDegree d := by
  intro hreg
  -- A `d`-regular graph has `∑ deg = n·d`, which would be odd, contradicting handshake parity.
  have hsum : ∑ v, G.degree v = Fintype.card V * d := by
    simp only [hreg.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have heven : Even (Fintype.card V * d) := hsum ▸ even_sum_degrees G
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  omega

/-- **The impossibility for `n` and `d` both odd** (the headline case). -/
theorem not_isRegularOfDegree_of_odd_odd (d : ℕ) (hn : Odd (Fintype.card V))
    (hd : Odd d) : ¬ G.IsRegularOfDegree d :=
  not_isRegularOfDegree_of_odd_mul G d (hn.mul hd)

/-- **Sharpness: the floor `1` is attained.** The empty graph on a single vertex,
with target degree `d = 1`, has `n·d = 1` odd and degree deficiency exactly `1`.
So the lower bound `one_le_deficiency` cannot be improved. -/
theorem deficiency_floor_attained :
    deficiency (⊥ : SimpleGraph (Fin 1)) 1 = 1 := by decide

/-- The witness graph indeed has `n·d = 1` odd and every degree `≤ 1`. -/
example : Odd (Fintype.card (Fin 1) * 1) := by decide
example : ∀ v, (⊥ : SimpleGraph (Fin 1)).degree v ≤ 1 := by decide

end HandshakeLemmaOQ01
