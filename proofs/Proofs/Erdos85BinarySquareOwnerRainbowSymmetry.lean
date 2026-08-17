import Proofs.Erdos85OrderSixtyFourRoutingCensusDichotomy

/-! # Symmetries of owner-color rainbow triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cyclically rotating the three vertices of an owner rainbow cyclically
rotates its three owner colors. -/
theorem routingOwnerRainbow_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    routingOwnerRainbow G d e f c ↔ routingOwnerRainbow G d f c e := by
  constructor
  · rintro ⟨y₁, y₂, y₃, h₁₂, h₂₃, h₃₁, he, hf, hc⟩
    exact ⟨y₂, y₃, y₁, h₂₃, h₃₁, h₁₂, hf, hc, he⟩
  · rintro ⟨y₁, y₂, y₃, h₁₂, h₂₃, h₃₁, hf, hc, he⟩
    exact ⟨y₃, y₁, y₂, h₃₁, h₁₂, h₂₃, he, hf, hc⟩

/-- Reversing the three vertices of an owner rainbow transposes its first
two owner colors. -/
theorem routingOwnerRainbow_swap_first_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    routingOwnerRainbow G d e f c ↔ routingOwnerRainbow G d f e c := by
  constructor
  · rintro ⟨y₁, y₂, y₃, h₁₂, h₂₃, h₃₁, he, hf, hc⟩
    exact ⟨y₃, y₂, y₁, h₂₃.symm, h₁₂.symm, h₃₁.symm,
      hf.symm, he.symm, hc.symm⟩
  · rintro ⟨y₁, y₂, y₃, h₁₂, h₂₃, h₃₁, hf, he, hc⟩
    exact ⟨y₃, y₂, y₁, h₂₃.symm, h₁₂.symm, h₃₁.symm,
      he.symm, hf.symm, hc.symm⟩

/-- In particular, an owner rainbow depends only on the unordered triple of
owner colors: the final two colors may also be exchanged. -/
theorem routingOwnerRainbow_swap_last_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    routingOwnerRainbow G d e f c ↔ routingOwnerRainbow G d e c f := by
  constructor
  · rintro ⟨y₁, y₂, y₃, h₁₂, h₂₃, h₃₁, he, hf, hc⟩
    exact ⟨y₂, y₁, y₃, h₁₂.symm, h₃₁.symm, h₂₃.symm,
      he.symm, hc.symm, hf.symm⟩
  · rintro ⟨y₁, y₂, y₃, h₁₂, h₂₃, h₃₁, he, hc, hf⟩
    exact ⟨y₂, y₁, y₃, h₁₂.symm, h₃₁.symm, h₂₃.symm,
      he.symm, hf.symm, hc.symm⟩

end

end Erdos85
