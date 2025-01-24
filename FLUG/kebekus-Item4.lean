import Mathlib.Analysis.SpecialFunctions.Exp


-- # ENat und WithTop ℤ

-- ## Example 1

-- I am puzzled. Is it really that complicated?
lemma WithTopCoe
  {n : WithTop ℕ} :
  WithTop.map (Nat.cast : ℕ → ℤ) n = 0 → n = 0 := by
  cases n
  <;> simp


-- ## Example 2

-- Easy
lemma toNat_add {a b : ENat} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).toNat = a.toNat + b.toNat :=
  ENat.toNat_add ha hb


-- Complicated. Even the formulation needs a lemma
lemma ne_top_add_ne_top {a b : WithTop ℤ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + b ≠ ⊤ := by
  simp; tauto

lemma untop_add {a b : WithTop ℤ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untop (ne_top_add_ne_top ha hb) = a.untop ha + (b.untop hb) := by
  rw [WithTop.untop_eq_iff]
  rw [WithTop.coe_add]
  rw [WithTop.coe_untop]
  rw [WithTop.coe_untop]


-- Unclear to me. Is this easy?
lemma untop'_add {a b : WithTop ℤ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untop' 0 = a.untop' 0 + b.untop' 0 := by
  -- Proof by Commelin
  rw [WithTop.ne_top_iff_exists] at ha hb
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  norm_cast

-- ## Example 3

-- Easy
lemma toNat'_of_ne_top_eq_coe {a : ENat} (ha : a ≠ ⊤) :
    a.toNat = a := by
  simpa


-- Easy
lemma untop_of_ne_top_eq_coe {a : WithTop ℤ} (ha : a ≠ ⊤) :
    a.untop ha = a := by
  simp


-- Complicated. Isn't there an easier proof?
lemma untop'_of_ne_top_eq_coe {a : WithTop ℤ} {d : ℤ} (ha : a ≠ ⊤) :
    WithTop.untop' d a = a := by
  -- Simplified proof by Commelin
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.1 ha
  simp

-- ## Example 4

-- Unclear to me. Is there an easy proof?
lemma untop'_and_untop {a : WithTop ℕ} (ha : a ≠ ⊤) :
    a.untop ha = a.untop' 0 := by
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.1 ha
  simp



-- ## Example 5

-- Easy
lemma add_mul_enat {a : ℕ} {b : ENat} :
    a * b + b = (a + 1) * b := by
  rw [add_one_mul]


-- Unclear to me. Is there an easy proof?
lemma add_mul_withTop {a : ℕ} {b : WithTop ℤ} :
    a * b + b = (a + 1) * b := by
  cases b
  · simp
    exact rfl
  · norm_cast
    simp
    ring
