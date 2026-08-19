import Proofs.Erdos85SizeTwoEigenlineCyclicThreeFiberSubsystem

/-!
# Reciprocity transpose inside a reduced fiber subsystem

The existing matching transpose lemmas are phrased for a globally reciprocal
full code.  The exact q=8 core deliberately retains reciprocity only at three
source fibers.  Here reversal is rebuilt for raw routing data: whenever
reciprocity holds at both `t` and `s`, routes from `t` to `s` are equivalent
to routes from `s` to `t`.
-/

namespace Erdos85

noncomputable section

/-- A routed dart whose source and target difference fibers are fixed. -/
structure SizeTwoCyclicRoutingFiberDart
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t s : sizeTwoAllowedDifference q a) where
  base : ZMod q
  row : SizeTwoAdmissibleTargetRow q t.1
  target_eq : data.targetDifference base t row = s

private theorem sizeTwoCyclicRoutingFiberDart_pair_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoCyclicRoutingFiberDart data t s =>
      (w.base, w.row.1)) := by
    intro u v h
    have hbase : u.base = v.base := congrArg Prod.fst h
    have hrowVal : u.row.1 = v.row.1 := congrArg Prod.snd h
    have hrow : u.row = v.row := Subtype.ext hrowVal
    cases u with
    | mk ubase urow utarget =>
      cases v with
      | mk vbase vrow vtarget =>
        dsimp at hbase hrow
        subst vbase
        subst vrow
        rfl

noncomputable instance SizeTwoCyclicRoutingFiberDart.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a} :
    Fintype (SizeTwoCyclicRoutingFiberDart data t s) :=
  Fintype.ofInjective (fun w => (w.base, w.row.1))
    sizeTwoCyclicRoutingFiberDart_pair_injective

/-- Reverse a fixed-fiber dart using reciprocity at its source fiber. -/
def SizeTwoCyclicRoutingFiberDart.reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t)
    (w : SizeTwoCyclicRoutingFiberDart data t s) :
    SizeTwoCyclicRoutingFiberDart data s t := by
  rcases w with ⟨base, row, rfl⟩
  let reverseRow : SizeTwoAdmissibleTargetRow q
      (data.targetDifference base t row).1 :=
    ⟨-row.1, data.reverse_admissible base t row⟩
  refine ⟨base + row.1, reverseRow, ?_⟩
  apply Subtype.ext
  have hrecip := ht base row
  have hcolumn := data.target_column_eq
    (base + row.1) (data.targetDifference base t row) reverseRow
  change (-row.1) +
      (data.targetDifference (base + row.1)
        (data.targetDifference base t row) reverseRow).1 =
    (data.perm (base + row.1)
      (data.targetDifference base t row) reverseRow).1 at hcolumn
  change (data.perm (base + row.1)
      (data.targetDifference base t row)
      ⟨-row.1, data.reverse_admissible base t row⟩).1 =
    t.1 - row.1 at hrecip
  have hrecip' : (data.perm (base + row.1)
      (data.targetDifference base t row) reverseRow).1 =
      t.1 - row.1 := by simpa only [reverseRow] using hrecip
  change (data.targetDifference (base + row.1)
    (data.targetDifference base t row) reverseRow).1 = t.1
  calc
    _ = row.1 + ((-row.1) +
        (data.targetDifference (base + row.1)
          (data.targetDifference base t row) reverseRow).1) := by abel
    _ = row.1 + (data.perm (base + row.1)
        (data.targetDifference base t row) reverseRow).1 := by rw [hcolumn]
    _ = row.1 + (t.1 - row.1) := by rw [hrecip']
    _ = t.1 := by abel

@[simp] theorem SizeTwoCyclicRoutingFiberDart.reverse_base
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t)
    (w : SizeTwoCyclicRoutingFiberDart data t s) :
    (w.reverse ht).base = w.base + w.row.1 := by
  rcases w with ⟨base, row, rfl⟩
  rfl

@[simp] theorem SizeTwoCyclicRoutingFiberDart.reverse_row_val
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t)
    (w : SizeTwoCyclicRoutingFiberDart data t s) :
    (w.reverse ht).row.1 = -w.row.1 := by
  rcases w with ⟨base, row, rfl⟩
  rfl

@[ext] theorem SizeTwoCyclicRoutingFiberDart.ext
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    {u v : SizeTwoCyclicRoutingFiberDart data t s}
    (hbase : u.base = v.base) (hrow : u.row = v.row) : u = v := by
  cases u
  cases v
  simp_all

/-- Reversing twice returns the original fixed-fiber dart. -/
theorem SizeTwoCyclicRoutingFiberDart.reverse_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t) (hs : data.ReciprocityAt s)
    (w : SizeTwoCyclicRoutingFiberDart data t s) :
    (w.reverse ht).reverse hs = w := by
  rcases w with ⟨base, row, rfl⟩
  apply SizeTwoCyclicRoutingFiberDart.ext
  · simp
  · apply Subtype.ext
    simp

/-- Route reversal is an equivalence between opposite selected fiber pairs. -/
def sizeTwoCyclicRoutingFiberDartReverseEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t) (hs : data.ReciprocityAt s) :
    SizeTwoCyclicRoutingFiberDart data t s ≃
      SizeTwoCyclicRoutingFiberDart data s t where
  toFun w := w.reverse ht
  invFun w := w.reverse hs
  left_inv := SizeTwoCyclicRoutingFiberDart.reverse_reverse ht hs
  right_inv := SizeTwoCyclicRoutingFiberDart.reverse_reverse hs ht

/-- The selected-fiber route incidence matrix is symmetric wherever both
fiber reciprocity laws are available. -/
theorem sizeTwoCyclicRoutingFiberDart_card_symm
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t) (hs : data.ReciprocityAt s) :
    Fintype.card (SizeTwoCyclicRoutingFiberDart data t s) =
      Fintype.card (SizeTwoCyclicRoutingFiberDart data s t) :=
  Fintype.card_congr (sizeTwoCyclicRoutingFiberDartReverseEquiv ht hs)

/-- Restrict fixed-fiber darts to one source-row displacement. -/
abbrev SizeTwoCyclicRoutingFiberRowDart
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t s : sizeTwoAllowedDifference q a)
    (r : ZMod q) :=
  {w : SizeTwoCyclicRoutingFiberDart data t s // w.row.1 = r}

/-- Displacement-resolved reversal: the `r` slice from `t` to `s` is the
`-r` slice from `s` back to `t`. -/
def sizeTwoCyclicRoutingFiberRowDartReverseEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t) (hs : data.ReciprocityAt s)
    (r : ZMod q) :
    SizeTwoCyclicRoutingFiberRowDart data t s r ≃
      SizeTwoCyclicRoutingFiberRowDart data s t (-r) where
  toFun w := ⟨w.1.reverse ht, by
    simp [w.2]⟩
  invFun w := ⟨w.1.reverse hs, by
    simpa using congrArg Neg.neg w.2⟩
  left_inv w := by
    apply Subtype.ext
    exact SizeTwoCyclicRoutingFiberDart.reverse_reverse ht hs w.1
  right_inv w := by
    apply Subtype.ext
    exact SizeTwoCyclicRoutingFiberDart.reverse_reverse hs ht w.1

/-- Cardinal form of displacement-resolved reciprocity. -/
theorem sizeTwoCyclicRoutingFiberRowDart_card_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {data : SizeTwoCyclicRoutingData q a}
    {t s : sizeTwoAllowedDifference q a}
    (ht : data.ReciprocityAt t) (hs : data.ReciprocityAt s)
    (r : ZMod q) :
    Fintype.card (SizeTwoCyclicRoutingFiberRowDart data t s r) =
      Fintype.card (SizeTwoCyclicRoutingFiberRowDart data s t (-r)) :=
  Fintype.card_congr
    (sizeTwoCyclicRoutingFiberRowDartReverseEquiv ht hs r)

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicRoutingFiberDart.reverse_reverse
#print axioms Erdos85.sizeTwoCyclicRoutingFiberDart_card_symm
#print axioms Erdos85.sizeTwoCyclicRoutingFiberRowDart_card_reverse
