-- Test: API availability for resolving RH sorry
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

open Complex

-- Key API checks
#check @riemannZeta_neg_nat_eq_bernoulli  -- ζ(-k) = (-1)^k * B_{k+1} / (k+1)
#check @riemannZeta_two_mul_nat           -- ζ(2k) formula with Bernoulli
#check @riemannZeta_one_sub               -- functional equation
#check @riemannZeta_ne_zero_of_one_le_re  -- ζ(s) ≠ 0 for Re(s) ≥ 1
#check @riemannZeta_zero                  -- ζ(0) = -1/2
#check @riemannZeta_neg_two_mul_nat_add_one  -- ζ(-2(n+1)) = 0

-- Check completedRiemannZeta
#check @completedRiemannZeta₀_one_sub     -- Λ₀(1-s) = Λ₀(s)
