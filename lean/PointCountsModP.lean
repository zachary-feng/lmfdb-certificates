import Mathlib
open Polynomial

def compute_points_mod_p (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  (Finset.univ.filter
    fun xy : (ZMod p) × (ZMod p) ↦
      letI x := xy.1
      letI y := xy.2
    y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6).card

def compute_points_mod_p' (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  ((Finset.univ : Finset (ZMod p)).val.map
    (fun x : ZMod p ↦
      legendreSym p
        ((a1 * x.val + a3) ^ 2
          + 4 * (x.val ^ 3 + a2 * x.val ^ 2 + a4 * x.val + a6))
        + 1)).sum

noncomputable def L_factor_at_p_good (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ[X]:=
  letI points_mod_p := compute_points_mod_p p h a1 a2 a3 a4 a6
  1 - (p - (points_mod_p : ℤ)) • X + p • X^2

def p_is_good (p : ℕ) (h : Fact p.Prime)
    (a1 a2 a3 a4 a6 : ℤ) : Bool :=
  letI E : WeierstrassCurve ℤ :=
    { a₁ := a1
      a₂ := a2
      a₃ := a3
      a₄ := a4
      a₆ := a6 }
  decide (¬ ((p : ℤ) ∣ E.Δ))

def p_is_split_multiplicative (p : ℕ) (h : Fact p.Prime)
    (a1 a2 a3 a4 a6 : ℤ) : Bool :=
  letI E : WeierstrassCurve ℤ :=
    { a₁ := a1
      a₂ := a2
      a₃ := a3
      a₄ := a4
      a₆ := a6 }
  letI b2 := a1 ^ 2 + 4 * a2
  letI b4 := a1 * a3 + 2 * a4
  letI b6 := a3 ^ 2 + 4 * a6
  letI c4 := b2 ^ 2 - 24 * b4
  letI c6 := -b2 ^ 3 + 36 * b2 * b4 - 216 * b6
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ c4) ∧ (legendreSym p (-c6) = 1)

def p_is_non_split_multiplicative (p : ℕ) (h : Fact p.Prime)
    (a1 a2 a3 a4 a6 : ℤ) : Bool :=
  letI E : WeierstrassCurve ℤ :=
    { a₁ := a1
      a₂ := a2
      a₃ := a3
      a₄ := a4
      a₆ := a6 }
  letI b2 := a1 ^ 2 + 4 * a2
  letI b4 := a1 * a3 + 2 * a4
  letI b6 := a3 ^ 2 + 4 * a6
  letI c4 := b2 ^ 2 - 24 * b4
  letI c6 := -b2 ^ 3 + 36 * b2 * b4 - 216 * b6
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ c4) ∧ (legendreSym p (-c6) = -1)

-- Isogeny class: 21.a
-- Weierstrass curve: 21.a1
-- ⟨1, 0, 0, -784, -8515⟩
-- E : y^2 + xy = x^3 - 784x - 8515

-- p = 29 is a good prime for this curve

#eval p_is_good 29 (by decide) 1 0 0 (-784) (-8515)

theorem foo1 : L_factor_at_p_good 29 (by decide) 1 0 0 (-784) (-8515) = 1 + 2•X + 29•X^2 := by
  rw [L_factor_at_p_good, sub_eq_add_neg, ← neg_zsmul]
  rfl

theorem foo2 : p_is_good 29 (by decide) 1 0 0 (-784) (-8515) ∧
  L_factor_at_p_good 29 (by decide) 1 0 0 (-784) (-8515) = 1 + 2•X + 29•X^2 := by
  constructor
  · decide
  · exact foo1

-- p = 3 is a bad prime for this curve, split multiplicative reduction

#eval p_is_split_multiplicative 3 (by decide) 1 0 0 (-784) (-8515)

-- CONTINUE HERE...

-- p = 7 is a bad prime for this curve, non-split multiplicative reduction

#eval p_is_non_split_multiplicative 7 (by decide) 1 0 0 (-784) (-8515)

-- CONTINUE HERE...
