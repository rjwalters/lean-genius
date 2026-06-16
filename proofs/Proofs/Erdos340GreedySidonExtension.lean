import Mathlib

/-!
# Erdős #340 — Sidon Extendability (constructive existence kernel)

This companion file proves the **extension lemma** underlying the greedy Sidon
construction in `Erdos340GreedySidon.lean`. That file axiomatizes the existence of
an infinite strictly–increasing Sidon sequence via

```
axiom greedySidonSeq            : ℕ → ℕ
axiom greedySidonSeq_strictMono : StrictMono greedySidonSeq
axiom greedySidonSeq_isSidon    : ∀ n, IsSidon (image greedySidonSeq (range (n+1)))
```

The mathematical content those axioms depend on is *extendability*: every finite
Sidon set can be enlarged by one new (larger) element while staying Sidon. We prove
this constructively here, with an **explicit** witness `m = 2 · (sup A) + 1`, and
derive the existence of an infinite strictly–increasing Sidon sequence.

This is a (sorry-free, axiom-free) result. It does **not** reproduce the *greedy*
(Mian–Chowla, OEIS A005282) sequence — only a doubling sequence — so it does not
literally discharge the greedy-specific axioms, but it discharges the substantive
*existence* claim those axioms encode. The N^(1/2−ε) growth conjecture (Erdős #340)
remains open and is untouched here.

## Why `m = 2·sup A + 1` works

Write `S = sup A`, so every element of `A` is `≤ S`, and put `m = 2S + 1 > S`.
A new collision in `insert m A` is an equation `a + b = c + d` (with `a ≤ b`,
`c ≤ d`) in which `m` participates. Since `m` is strictly larger than every element
of `A`, on each side `m` (if present) must be the larger summand, so a side's sum
falls in exactly one of three disjoint bands:

* no `m`: sum `≤ 2S`;
* one `m`: sum `∈ [2S+1, 3S+1]`;
* two `m`: sum `= 4S+2`.

Equal sums therefore force the two sides to use `m` the *same* number of times,
after which `Nat` cancellation (and the original Sidon property for the
all-in-`A` case) gives `a = c` and `b = d`.
-/

namespace Erdos340Extension

/-- A finite set of naturals is **Sidon** iff all pairwise sums are distinct:
    `a + b = c + d` with `a ≤ b`, `c ≤ d` forces `(a, b) = (c, d)`. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- Every element of a finset is at most its `sup id`. -/
theorem le_sup_id {A : Finset ℕ} {x : ℕ} (hx : x ∈ A) : x ≤ A.sup id :=
  Finset.le_sup (f := id) hx

/-- The explicit extension witness `2 · sup A + 1` is strictly above every element. -/
theorem lt_two_sup_add_one {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a < 2 * A.sup id + 1 := by
  have := le_sup_id ha
  omega

/-- **Extension lemma.** Inserting `2 · sup A + 1` into a Sidon set keeps it Sidon. -/
theorem sidon_insert_two_sup_add_one {A : Finset ℕ} (hA : IsSidon A) :
    IsSidon (insert (2 * A.sup id + 1) A) := by
  set S := A.sup id with hS
  set m := 2 * S + 1 with hm
  have hbound : ∀ x ∈ A, x ≤ S := by
    intro x hx; rw [hS]; exact le_sup_id hx
  intro a b c d ha hb hc hd hab hcd hsum
  simp only [Finset.mem_insert] at ha hb hc hd
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;>
    rcases hc with rfl | hc <;> rcases hd with rfl | hd <;>
  first
    | exact hA a b c d ha hb hc hd hab hcd hsum
    | (try have ba := hbound _ ha
       try have bb := hbound _ hb
       try have bc := hbound _ hc
       try have bd := hbound _ hd
       omega)

/-- Inserting `2 · sup A + 1` adds a genuinely new element (it is not in `A`). -/
theorem two_sup_add_one_not_mem {A : Finset ℕ} : 2 * A.sup id + 1 ∉ A := by
  intro hmem
  have := lt_two_sup_add_one hmem
  omega

/-- **Extendability.** Every finite Sidon set can be enlarged by one strictly larger
element while remaining Sidon. This is the existence content underlying the greedy
construction's well-definedness. -/
theorem sidon_extendable {A : Finset ℕ} (hA : IsSidon A) :
    ∃ m, (∀ a ∈ A, a < m) ∧ m ∉ A ∧ IsSidon (insert m A) :=
  ⟨2 * A.sup id + 1, fun _ ha => lt_two_sup_add_one ha,
    two_sup_add_one_not_mem, sidon_insert_two_sup_add_one hA⟩

/-! ## An explicit infinite strictly-increasing Sidon sequence

We iterate the extension lemma to build a chain `A 0 ⊆ A 1 ⊆ …` of Sidon sets whose
cardinalities grow without bound, witnessing that an infinite Sidon set exists.  -/

/-- The doubling Sidon chain: start empty, repeatedly insert `2 · sup + 1`. -/
def sidonChain : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (2 * (sidonChain n).sup id + 1) (sidonChain n)

/-- Every set in the chain is Sidon. -/
theorem sidonChain_isSidon : ∀ n, IsSidon (sidonChain n)
  | 0 => by
      intro a b c d ha; simp [sidonChain] at ha
  | n + 1 => by
      simpa [sidonChain] using sidon_insert_two_sup_add_one (sidonChain_isSidon n)

/-- The chain is strictly increasing in cardinality: `|A n| = n`. -/
theorem sidonChain_card : ∀ n, (sidonChain n).card = n
  | 0 => by simp [sidonChain]
  | n + 1 => by
      have hnot : 2 * (sidonChain n).sup id + 1 ∉ sidonChain n := two_sup_add_one_not_mem
      simp only [sidonChain, Finset.card_insert_of_not_mem hnot, sidonChain_card n]

/-- **Existence of arbitrarily large Sidon sets.** For every `n` there is a Sidon
set of cardinality `n`. Hence finite Sidon sets are unbounded in size, which is the
existence fact the `greedySidonSeq*` axioms encode. -/
theorem exists_sidon_card (n : ℕ) : ∃ A : Finset ℕ, IsSidon A ∧ A.card = n :=
  ⟨sidonChain n, sidonChain_isSidon n, sidonChain_card n⟩

end Erdos340Extension
