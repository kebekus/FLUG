import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

lemma awk₁ : |2 * π| * |(2 * π)⁻¹| = 1 := by
  --apply?
  --rw [abs_inv, mul_inv_cancel₀]
  positivity
