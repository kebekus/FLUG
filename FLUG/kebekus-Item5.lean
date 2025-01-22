import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

lemma awk₁ : |2 * π| * |(2 * π)⁻¹| = 1 := by
  rw [abs_mul, abs_inv, abs_mul]
  rw [abs_of_pos pi_pos]
  simp [pi_ne_zero]
  ring_nf
  simp [pi_ne_zero]
