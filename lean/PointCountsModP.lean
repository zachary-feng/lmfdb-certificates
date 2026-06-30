import Mathlib

-- Isogeny class: 21.a
-- Weierstrass curve: 21.a1
-- ⟨1, 0, 0, -784, -8515⟩
-- E : y^2 + xy = x^3 - 784x - 8515

local instance : Fact (Nat.Prime 29) := by decide +kernel

def compute_ap (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) := (Finset.univ.filter
  fun xy : (ZMod p) × (ZMod p) ↦
  letI x := xy.1
  letI y := xy.2
  y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6).card

theorem bar3 : compute_ap 29 (by decide) 1 0 0 (-784) (-8515) = 31 := by decide

open Polynomial

noncomputable def bar4 (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ[X]:=
  letI ap := compute_ap p h a1 a2 a3 a4 a6
  1 - (p - (ap : ℤ)) • X + p • X^2

theorem bar5 : bar4 29 (by decide) 1 0 0 (-784) (-8515) = 1 + 2•X + 29•X^2 := by
  rw [bar4, sub_eq_add_neg, ← neg_zsmul]
  rfl
