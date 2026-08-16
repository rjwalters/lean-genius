import Proofs.Erdos85OddKeyLabelGraph

/-! # Parity of the odd exchanged-key support size -/

namespace Erdos85

noncomputable section

/-- The number of keys of odd multiplicity has the same parity as the total
number of nonconstant matching edges. -/
theorem even_card_oddExchangedKeySupport_iff
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) :
    Even (oddExchangedKeySupport
      (exchangedMissPairMultiplicity mate label)).card ↔
      Even (nonconstantMatchingEdgeSources mate label).card := by
  rw [oddExchangedKeySupport,
    even_card_filter_odd_iff_even_sum]
  rw [sum_exchangedMissPairMultiplicity_over_keys]

theorem odd_card_oddExchangedKeySupport_iff
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) :
    Odd (oddExchangedKeySupport
      (exchangedMissPairMultiplicity mate label)).card ↔
      Odd (nonconstantMatchingEdgeSources mate label).card := by
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
  exact not_congr (even_card_oddExchangedKeySupport_iff mate label)

/-- Profile-facing form: once the total number of nonconstant matching edges
is identified with `n`, the support-size parity is exactly the parity of `n`. -/
theorem even_card_oddExchangedKeySupport_iff_of_card_eq
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (n : ℕ)
    (hcard : (nonconstantMatchingEdgeSources mate label).card = n) :
    Even (oddExchangedKeySupport
      (exchangedMissPairMultiplicity mate label)).card ↔ Even n := by
  rw [even_card_oddExchangedKeySupport_iff, hcard]

theorem odd_card_oddExchangedKeySupport_iff_of_card_eq
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (n : ℕ)
    (hcard : (nonconstantMatchingEdgeSources mate label).card = n) :
    Odd (oddExchangedKeySupport
      (exchangedMissPairMultiplicity mate label)).card ↔ Odd n := by
  rw [odd_card_oddExchangedKeySupport_iff, hcard]

end

end Erdos85
