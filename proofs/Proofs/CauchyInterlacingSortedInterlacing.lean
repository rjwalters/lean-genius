import Mathlib
import Proofs.CauchyInterlacingPoincareCompression

/-!
# Termwise interlacing of the *sorted* eigenvalue lists over a reducing subspace

The file `CauchyInterlacingPoincareCompression.lean` proves — symmetry-free — that over a
reducing subspace `H` the eigenvalue multisets partition,
`(charpoly (compress T H)).roots ≤ (charpoly T).roots`
(`roots_charpoly_compress_le_of_reducing`).  That is a statement about **multisets**; it
records containment but not the *order* in which the eigenvalues appear.  The classical
Cauchy-interlacing picture is a statement about the **descending-sorted** eigenvalue lists:
the `i`-th largest eigenvalue of a compression is bounded by the `i`-th largest eigenvalue
of the ambient operator.

This file supplies the missing order-theoretic bridge and reads it off on eigenvalues:

* `Multiset.sortDesc_getElem_le_of_le` — the abstract **monotone-selection** lemma: for any
  `LinearOrder`, if `s ≤ t` as multisets then the `i`-th largest element of `s` is `≤` the
  `i`-th largest element of `t`.  (Weak majorization by containment.)  This is field-agnostic
  reusable infrastructure, absent from Mathlib.
* `sortDesc_roots_compress_le_of_reducing` (and its `Hᗮ` companion) — the eigenvalue reading
  over `ℝ`: the `i`-th largest real eigenvalue (root of the charpoly, with algebraic
  multiplicity) of the `H`-compression is `≤` the `i`-th largest real eigenvalue of `T`.
  Symmetry-free; for self-adjoint `T` the charpoly splits into real roots, so these roots are
  the full eigenvalue list and this is genuine one-sided Cauchy interlacing.

The abstract lemma's proof is a clean counting argument: the first `i+1` entries of the sorted
list of `s` are all `≥ a := sₖ`, so at least `i+1` elements of `s` — hence of `t ≥ s` — are
`≥ a`; but if the `i`-th largest of `t` were `< a`, only the first `i` entries of `t`'s sorted
list could be `≥ a`, bounding that count by `i`, a contradiction.
-/

open scoped InnerProductSpace
open CauchyInterlacing.Compression CauchyInterlacing.PoincareCompression

namespace Multiset

variable {α : Type*} [LinearOrder α]

/-- The descending sort's indexed access is antitone in the index: earlier entries are `≥`
later ones.  Read straight off `Multiset.pairwise_sort` for the relation `(· ≥ ·)`. -/
private theorem sortDesc_getElem_antitone (s : Multiset α) {j k : ℕ}
    (hj : j < (s.sort (· ≥ ·)).length) (hk : k < (s.sort (· ≥ ·)).length) (hjk : j ≤ k) :
    (s.sort (· ≥ ·))[k] ≤ (s.sort (· ≥ ·))[j] := by
  rcases eq_or_lt_of_le hjk with h | h
  · subst h; exact le_refl _
  · exact List.pairwise_iff_getElem.mp (Multiset.pairwise_sort (s := s) (r := (· ≥ ·))) j k hj hk h

/-- Every element of the length-`(i+1)` prefix of the descending sort is `≥` the `i`-th
entry (the smallest entry of that prefix). -/
private theorem sortDesc_le_of_mem_take (s : Multiset α) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) {x : α}
    (hx : x ∈ (s.sort (· ≥ ·)).take (i + 1)) :
    (s.sort (· ≥ ·))[i] ≤ x := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  have hklen : k < (s.sort (· ≥ ·)).length := by
    have := hk; rw [List.length_take] at this; omega
  have hki : k ≤ i := by
    have := hk; rw [List.length_take] at this; omega
  rw [List.getElem_take]
  exact sortDesc_getElem_antitone s hklen hi hki

/-- Every element of the `i`-th tail of the descending sort is `≤` the `i`-th entry. -/
private theorem sortDesc_ge_of_mem_drop (s : Multiset α) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) {x : α}
    (hx : x ∈ (s.sort (· ≥ ·)).drop i) :
    x ≤ (s.sort (· ≥ ·))[i] := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  have hklen : i + k < (s.sort (· ≥ ·)).length := by
    have := hk; rw [List.length_drop] at this; omega
  rw [List.getElem_drop]
  exact sortDesc_getElem_antitone s hi hklen (Nat.le_add_right i k)

/-- **Monotone selection under multiset containment.**
For any `LinearOrder`, if `s ≤ t` as multisets then the `i`-th largest element of `s`
is `≤` the `i`-th largest element of `t` (both counted with multiplicity, descending):

  `(s.sort (· ≥ ·))[i] ≤ (t.sort (· ≥ ·))[i]`.

This is the "weak majorization by containment" order-statistic inequality, absent from
Mathlib.  Proof: the first `i+1` entries of `s`'s sorted list are all `≥ a := (s.sort)[i]`
(antitone), so `i+1 ≤ s.countP (a ≤ ·) ≤ t.countP (a ≤ ·)`; were `(t.sort)[i] < a`, only
`t`'s first `i` entries could be `≥ a`, forcing `t.countP (a ≤ ·) ≤ i` — a contradiction. -/
theorem sortDesc_getElem_le_of_le {s t : Multiset α} (h : s ≤ t) (i : ℕ)
    (hi : i < Multiset.card s) :
    (s.sort (· ≥ ·))[i]'(by rw [Multiset.length_sort]; exact hi) ≤
      (t.sort (· ≥ ·))[i]'(by
        rw [Multiset.length_sort]; exact hi.trans_le (Multiset.card_le_card h)) := by
  -- Abbreviations and index bounds.
  have hiS : i < (s.sort (· ≥ ·)).length := by rw [Multiset.length_sort]; exact hi
  have hiT : i < (t.sort (· ≥ ·)).length := by
    rw [Multiset.length_sort]; exact hi.trans_le (Multiset.card_le_card h)
  set a : α := (s.sort (· ≥ ·))[i] with ha
  classical
  -- Lower bound: at least `i+1` elements of `s` are `≥ a`.
  have hlow : i + 1 ≤ Multiset.countP (fun x => a ≤ x) s := by
    -- The length-`(i+1)` prefix is a sub-multiset of `s`, all of whose elements are `≥ a`.
    have hsub : (↑((s.sort (· ≥ ·)).take (i + 1)) : Multiset α) ≤ s := by
      calc (↑((s.sort (· ≥ ·)).take (i + 1)) : Multiset α)
          ≤ (↑(s.sort (· ≥ ·)) : Multiset α) :=
            Multiset.coe_le.mpr (List.take_sublist _ _).subperm
        _ = s := Multiset.sort_eq _ _
    have hall : ∀ x ∈ (↑((s.sort (· ≥ ·)).take (i + 1)) : Multiset α), a ≤ x := by
      intro x hx
      exact ha ▸ sortDesc_le_of_mem_take s i hiS (Multiset.mem_coe.mp hx)
    have hcard : Multiset.card (↑((s.sort (· ≥ ·)).take (i + 1)) : Multiset α) = i + 1 := by
      rw [Multiset.coe_card, List.length_take]
      omega
    calc i + 1 = Multiset.card (↑((s.sort (· ≥ ·)).take (i + 1)) : Multiset α) := hcard.symm
      _ = Multiset.countP (fun x => a ≤ x) (↑((s.sort (· ≥ ·)).take (i + 1)) : Multiset α) :=
          (Multiset.countP_eq_card.mpr hall).symm
      _ ≤ Multiset.countP (fun x => a ≤ x) s := Multiset.countP_le_of_le _ hsub
  -- Transport the lower bound to `t`.
  have hlowT : i + 1 ≤ Multiset.countP (fun x => a ≤ x) t :=
    hlow.trans (Multiset.countP_le_of_le _ h)
  -- Suppose the `i`-th largest of `t` were `< a`; derive `countP ≤ i`, a contradiction.
  by_contra hcon
  push_neg at hcon  -- hcon : (t.sort (· ≥ ·))[i] < a
  have hupp : Multiset.countP (fun x => a ≤ x) t ≤ i := by
    have hsplit : (↑(t.sort (· ≥ ·)) : Multiset α)
        = (↑((t.sort (· ≥ ·)).take i) : Multiset α) + (↑((t.sort (· ≥ ·)).drop i) : Multiset α) := by
      rw [Multiset.coe_add, List.take_append_drop]
    have hzero : Multiset.countP (fun x => a ≤ x)
        (↑((t.sort (· ≥ ·)).drop i) : Multiset α) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro x hx
      have hxle : x ≤ (t.sort (· ≥ ·))[i] :=
        sortDesc_ge_of_mem_drop t i hiT (Multiset.mem_coe.mp hx)
      exact not_le.mpr (lt_of_le_of_lt hxle hcon)
    have htake_le : Multiset.countP (fun x => a ≤ x)
        (↑((t.sort (· ≥ ·)).take i) : Multiset α) ≤ i := by
      calc Multiset.countP (fun x => a ≤ x) (↑((t.sort (· ≥ ·)).take i) : Multiset α)
          ≤ Multiset.card (↑((t.sort (· ≥ ·)).take i) : Multiset α) := Multiset.countP_le_card _ _
        _ = i := by rw [Multiset.coe_card, List.length_take]; omega
    calc Multiset.countP (fun x => a ≤ x) t
        = Multiset.countP (fun x => a ≤ x) (↑(t.sort (· ≥ ·)) : Multiset α) := by
          rw [Multiset.sort_eq]
      _ = Multiset.countP (fun x => a ≤ x) (↑((t.sort (· ≥ ·)).take i) : Multiset α)
            + Multiset.countP (fun x => a ≤ x) (↑((t.sort (· ≥ ·)).drop i) : Multiset α) := by
          rw [hsplit, Multiset.countP_add]
      _ ≤ i := by rw [hzero]; simpa using htake_le
  omega

/-- **Co-selection under multiset containment (the lower interlacing bound).**
For any `LinearOrder`, if `s ≤ t` as multisets then the `i`-th largest element of `s`
is `≥` the `(i + (card t − card s))`-th largest element of `t` (both descending, with
multiplicity):

  `(t.sort (· ≥ ·))[i + (card t − card s)] ≤ (s.sort (· ≥ ·))[i]`.

This is the co-selection companion of `sortDesc_getElem_le_of_le` — the shift by the
cardinality gap `card t − card s` is exactly the index displacement of the classical
two-sided Cauchy interlacing inequality.  Proof is the mirror of the upper bound, counting
elements `≤ a := (s.sort)[i]` from the tail: the drop-`i` tail of `s` gives
`card s − i ≤ countP (· ≤ a) s ≤ countP (· ≤ a) t`, while if `(t.sort)[i+d] > a` the
length-`(i+d+1)` prefix of `t` is entirely `> a`, forcing `countP (· ≤ a) t ≤ card s − i − 1`
— a contradiction. -/
theorem sortDesc_getElem_ge_of_le {s t : Multiset α} (h : s ≤ t) (i : ℕ)
    (hi : i < Multiset.card s) :
    (t.sort (· ≥ ·))[i + (Multiset.card t - Multiset.card s)]'(by
        rw [Multiset.length_sort]
        have := Multiset.card_le_card h; omega) ≤
      (s.sort (· ≥ ·))[i]'(by rw [Multiset.length_sort]; exact hi) := by
  have hcards : Multiset.card s ≤ Multiset.card t := Multiset.card_le_card h
  set d := Multiset.card t - Multiset.card s with hd
  have hiS : i < (s.sort (· ≥ ·)).length := by rw [Multiset.length_sort]; exact hi
  have hidT : i + d < (t.sort (· ≥ ·)).length := by rw [Multiset.length_sort]; omega
  set a : α := (s.sort (· ≥ ·))[i] with ha
  classical
  -- Lower bound: at least `card s - i` elements of `s` are `≤ a` (the drop-`i` tail).
  have hlow : Multiset.card s - i ≤ Multiset.countP (fun x => x ≤ a) s := by
    have hsub : (↑((s.sort (· ≥ ·)).drop i) : Multiset α) ≤ s := by
      calc (↑((s.sort (· ≥ ·)).drop i) : Multiset α)
          ≤ (↑(s.sort (· ≥ ·)) : Multiset α) :=
            Multiset.coe_le.mpr (List.drop_sublist _ _).subperm
        _ = s := Multiset.sort_eq _ _
    have hall : ∀ x ∈ (↑((s.sort (· ≥ ·)).drop i) : Multiset α), x ≤ a := by
      intro x hx
      exact ha ▸ sortDesc_ge_of_mem_drop s i hiS (Multiset.mem_coe.mp hx)
    have hcard : Multiset.card (↑((s.sort (· ≥ ·)).drop i) : Multiset α)
        = Multiset.card s - i := by
      rw [Multiset.coe_card, List.length_drop, Multiset.length_sort]
    calc Multiset.card s - i
        = Multiset.card (↑((s.sort (· ≥ ·)).drop i) : Multiset α) := hcard.symm
      _ = Multiset.countP (fun x => x ≤ a) (↑((s.sort (· ≥ ·)).drop i) : Multiset α) :=
          (Multiset.countP_eq_card.mpr hall).symm
      _ ≤ Multiset.countP (fun x => x ≤ a) s := Multiset.countP_le_of_le _ hsub
  have hlowT : Multiset.card s - i ≤ Multiset.countP (fun x => x ≤ a) t :=
    hlow.trans (Multiset.countP_le_of_le _ h)
  -- Suppose the `(i+d)`-th largest of `t` were `> a`; derive `countP (· ≤ a) t ≤ card s - i - 1`.
  by_contra hcon
  push_neg at hcon  -- hcon : a < (t.sort (· ≥ ·))[i + d]
  have hupp : Multiset.countP (fun x => x ≤ a) t ≤ Multiset.card s - i - 1 := by
    have hsplit : (↑(t.sort (· ≥ ·)) : Multiset α)
        = (↑((t.sort (· ≥ ·)).take (i + d + 1)) : Multiset α)
          + (↑((t.sort (· ≥ ·)).drop (i + d + 1)) : Multiset α) := by
      rw [Multiset.coe_add, List.take_append_drop]
    have hzero : Multiset.countP (fun x => x ≤ a)
        (↑((t.sort (· ≥ ·)).take (i + d + 1)) : Multiset α) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro x hx
      have hxge : (t.sort (· ≥ ·))[i + d] ≤ x :=
        sortDesc_le_of_mem_take t (i + d) hidT (Multiset.mem_coe.mp hx)
      exact not_le.mpr (lt_of_lt_of_le hcon hxge)
    have hdrop_le : Multiset.countP (fun x => x ≤ a)
        (↑((t.sort (· ≥ ·)).drop (i + d + 1)) : Multiset α) ≤ Multiset.card s - i - 1 := by
      calc Multiset.countP (fun x => x ≤ a)
              (↑((t.sort (· ≥ ·)).drop (i + d + 1)) : Multiset α)
          ≤ Multiset.card (↑((t.sort (· ≥ ·)).drop (i + d + 1)) : Multiset α) :=
            Multiset.countP_le_card _ _
        _ = Multiset.card s - i - 1 := by
            rw [Multiset.coe_card, List.length_drop, Multiset.length_sort]; omega
    calc Multiset.countP (fun x => x ≤ a) t
        = Multiset.countP (fun x => x ≤ a) (↑(t.sort (· ≥ ·)) : Multiset α) := by
          rw [Multiset.sort_eq]
      _ = Multiset.countP (fun x => x ≤ a)
              (↑((t.sort (· ≥ ·)).take (i + d + 1)) : Multiset α)
            + Multiset.countP (fun x => x ≤ a)
              (↑((t.sort (· ≥ ·)).drop (i + d + 1)) : Multiset α) := by
          rw [hsplit, Multiset.countP_add]
      _ ≤ Multiset.card s - i - 1 := by rw [hzero]; simpa using hdrop_le
  omega

end Multiset

namespace CauchyInterlacing.SortedInterlacing

open CauchyInterlacing.PoincareCompression

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **One-sided termwise Cauchy interlacing over a reducing subspace (`H`-block).**
Over `ℝ`, on a reducing subspace `H` the `i`-th largest real eigenvalue (root of the
characteristic polynomial, counted with algebraic multiplicity, descending) of the
`H`-compression is `≤` the `i`-th largest real eigenvalue of the ambient operator `T`:

  `((charpoly (compress T H)).roots.sort (· ≥ ·))[i]
      ≤ ((charpoly T).roots.sort (· ≥ ·))[i]`.

This is the *sorted-list* reading of the sub-multiset containment
`roots_charpoly_compress_le_of_reducing`, via the abstract monotone-selection lemma
`Multiset.sortDesc_getElem_le_of_le`.  Symmetry-free (the containment needs no symmetry);
for self-adjoint `T` the charpoly splits into real roots, so these roots are the full
eigenvalue list and this is the classical one-sided Cauchy interlacing bound. -/
theorem sortDesc_roots_compress_le_of_reducing
    {T : V →ₗ[ℝ] V} (H : Submodule ℝ V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) (i : ℕ)
    (hi : i < Multiset.card (LinearMap.charpoly (compress T H)).roots) :
    ((LinearMap.charpoly (compress T H)).roots.sort (· ≥ ·))[i]'(by
        rw [Multiset.length_sort]; exact hi) ≤
      ((LinearMap.charpoly T).roots.sort (· ≥ ·))[i]'(by
        rw [Multiset.length_sort]
        exact hi.trans_le (Multiset.card_le_card
          (roots_charpoly_compress_le_of_reducing H hH hHp))) :=
  Multiset.sortDesc_getElem_le_of_le (roots_charpoly_compress_le_of_reducing H hH hHp) i hi

/-- The `Hᗮ`-block companion of `sortDesc_roots_compress_le_of_reducing`: the `i`-th largest
real eigenvalue of the orthogonal compression is likewise `≤` the `i`-th largest of `T`. -/
theorem sortDesc_roots_orthogonal_compress_le_of_reducing
    {T : V →ₗ[ℝ] V} (H : Submodule ℝ V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) (i : ℕ)
    (hi : i < Multiset.card (LinearMap.charpoly (compress T Hᗮ)).roots) :
    ((LinearMap.charpoly (compress T Hᗮ)).roots.sort (· ≥ ·))[i]'(by
        rw [Multiset.length_sort]; exact hi) ≤
      ((LinearMap.charpoly T).roots.sort (· ≥ ·))[i]'(by
        rw [Multiset.length_sort]
        exact hi.trans_le (Multiset.card_le_card
          (roots_charpoly_orthogonal_compress_le_of_reducing H hH hHp))) :=
  Multiset.sortDesc_getElem_le_of_le
    (roots_charpoly_orthogonal_compress_le_of_reducing H hH hHp) i hi

/-- **Lower (co-selection) termwise Cauchy interlacing over a reducing subspace.**
The two-sided companion of `sortDesc_roots_compress_le_of_reducing`: over `ℝ`, on a reducing
subspace `H` the `i`-th largest eigenvalue (charpoly root, descending, with multiplicity) of
the `H`-compression is bounded *below* by the shifted eigenvalue of `T`:

  `((charpoly T).roots.sort (· ≥ ·))[i + (deg gap)] ≤ ((charpoly (compress T H)).roots.sort (· ≥ ·))[i]`,

where the index gap is `card (charpoly T).roots − card (charpoly (compress T H)).roots`
(the codimension when the charpolys split).  Together with
`sortDesc_roots_compress_le_of_reducing` this is the full two-sided sorted Cauchy interlacing
`λ_{i+gap}(T) ≤ λ_i(H-block) ≤ λ_i(T)` on the algebraic (charpoly-root) track.  Read straight
off the abstract co-selection lemma `Multiset.sortDesc_getElem_ge_of_le` applied to the
sub-multiset containment `roots_charpoly_compress_le_of_reducing`. -/
theorem sortDesc_roots_compress_ge_of_reducing
    {T : V →ₗ[ℝ] V} (H : Submodule ℝ V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) (i : ℕ)
    (hi : i < Multiset.card (LinearMap.charpoly (compress T H)).roots) :
    ((LinearMap.charpoly T).roots.sort (· ≥ ·))[i + (Multiset.card (LinearMap.charpoly T).roots
        - Multiset.card (LinearMap.charpoly (compress T H)).roots)]'(by
        rw [Multiset.length_sort]
        have := Multiset.card_le_card (roots_charpoly_compress_le_of_reducing H hH hHp)
        omega) ≤
      ((LinearMap.charpoly (compress T H)).roots.sort (· ≥ ·))[i]'(by
        rw [Multiset.length_sort]; exact hi) :=
  Multiset.sortDesc_getElem_ge_of_le (roots_charpoly_compress_le_of_reducing H hH hHp) i hi

/-- Over `ℝ` the real-part map is the identity on a multiset of reals, so mapping the
charpoly roots through `RCLike.re` (as Mathlib's `sort_roots_charpoly_eq_eigenvalues` does)
leaves them unchanged.  This is the only wiring needed to read the real charpoly-root list as
the geometric eigenvalue list. -/
private theorem multiset_map_re_real (s : Multiset ℝ) : s.map RCLike.re = s := by
  have h : ∀ x ∈ s, RCLike.re x = id x := fun x _ => RCLike.re_to_real
  rw [Multiset.map_congr rfl h, Multiset.map_id]

/-- **Geometric one-sided Cauchy interlacing on Mathlib's `IsSymmetric.eigenvalues`.**
The bridge from the algebraic (charpoly-root) track to the genuine spectral eigenvalue
function.  For a self-adjoint `T` on the `n`-dimensional real inner-product space `V` and a
*reducing* subspace `H` (both `H` and `Hᗮ` are `T`-invariant) of dimension `m`, the honest
`H`-compression `compress T H : H →ₗ H` is self-adjoint (`isSymmetric_compress`), and its
`i`-th largest eigenvalue is bounded by the `i`-th largest eigenvalue of `T`:

  `λ_i(compress T H) ≤ λ_i(T)`,

where `λ_i` is Mathlib's descending-indexed `LinearMap.IsSymmetric.eigenvalues`.

This unifies the two tracks the file family develops.  The algebraic side
(`sortDesc_roots_compress_le_of_reducing`) proves the termwise bound on the *sorted charpoly-root
lists*; Mathlib's `sort_roots_charpoly_eq_eigenvalues` identifies, for a self-adjoint operator over
`ℝ`, that descending-sorted root list with `List.ofFn (eigenvalues)` (the real-part map being the
identity here, `multiset_map_re_real`).  Reading the algebraic bound off index `i` through that
identification yields the classical Cauchy interlacing bound stated directly on the spectral
eigenvalues. -/
theorem eigenvalues_compress_le_of_reducing
    {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric) (H : Submodule ℝ V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    {n m : ℕ} (hn : Module.finrank ℝ V = n) (hm : Module.finrank ℝ H = m)
    (i : ℕ) (hi : i < m) :
    (isSymmetric_compress hT H).eigenvalues hm ⟨i, hi⟩
      ≤ hT.eigenvalues hn ⟨i, by have := Submodule.finrank_le H (R := ℝ); omega⟩ := by
  -- The compression's charpoly splits, so its root multiset has cardinality `m = dim H`.
  have hcardm : Multiset.card (LinearMap.charpoly (compress T H)).roots = m := by
    rw [(isSymmetric_compress hT H).roots_charpoly_eq_eigenvalues hm]; simp
  have hi' : i < Multiset.card (LinearMap.charpoly (compress T H)).roots := hcardm ▸ hi
  -- Algebraic sorted one-sided interlacing on the charpoly-root lists.
  have halg := sortDesc_roots_compress_le_of_reducing H hH hHp i hi'
  -- Identify each descending-sorted real root list with the eigenvalue list.
  have hbridgeC : (LinearMap.charpoly (compress T H)).roots.sort (· ≥ ·)
      = List.ofFn ((isSymmetric_compress hT H).eigenvalues hm) := by
    have h := (isSymmetric_compress hT H).sort_roots_charpoly_eq_eigenvalues hm
    rwa [multiset_map_re_real] at h
  have hbridgeT : (LinearMap.charpoly T).roots.sort (· ≥ ·)
      = List.ofFn (hT.eigenvalues hn) := by
    have h := hT.sort_roots_charpoly_eq_eigenvalues hn
    rwa [multiset_map_re_real] at h
  -- Read the algebraic bound off index `i` through the identifications.
  simp only [hbridgeC, hbridgeT, List.getElem_ofFn] at halg
  exact halg

end CauchyInterlacing.SortedInterlacing
