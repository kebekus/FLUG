import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}



-- # Example 1, Mathlib.Analysis.Calculus.FDeriv.Add

@[fun_prop]
theorem Differentiable.const_smul' (h : Differentiable 𝕜 f) (c : 𝕜) :
    Differentiable 𝕜 (c • f) := by
  have : c • f = fun x ↦ c • f x := rfl
  rw [this]
  exact Differentiable.const_smul h c


-- # Example 2, Casting Nat, Int and Real

lemma t₀ {n : ℤ} :
    n * Real.pi = 0 := by
  sorry

lemma t₁ {n m : ℕ} :
    (n + m) * Real.pi = 0 := by
  rw [t₀] -- I find it hard to apply t₀
  sorry
