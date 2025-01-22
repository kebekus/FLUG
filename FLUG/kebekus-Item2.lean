import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.IntervalIntegral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → 𝕜} {n : ℕ} {z z₀ : 𝕜}


-- # Teilaussagen und Spezialfälle: Privat oder öffentlich?

-- ## Beispiel 1: Mathlib.Analysis.Analytic.IsolatedZeros

lemma AnalyticAt.order_of_locallyZero_mul_analytic
  (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) (h'f : hf.order = ⊤) :
    (hf.mul hg).order = ⊤ := by
  sorry

/-- The order is additive when multiplying analytic functions -/
theorem AnalyticAt.order_mul
  (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (hf.mul hg).order = hf.order + hg.order := by
  sorry


-- ## Beispiel 2: Mathlib.MeasureTheory.Integral.IntervalIntegral

variable {f : ℝ → E}

lemma intervalIntegrable_of_even₀
  (h₁f : ∀ x, f x = f (-x))
  (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x)
  (t : ℝ) :
    IntervalIntegrable f volume 0 t := by
  sorry

theorem intervalIntegrable_of_even
  (h₁f : ∀ x, f x = f (-x))
  (h₂f : ∀ x, 0 < x → IntervalIntegrable f volume 0 x)
  (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  sorry
