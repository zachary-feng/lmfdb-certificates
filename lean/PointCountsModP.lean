import Mathlib

-- Isogeny class: 21.a
-- Weierstrass curve: 21.a1
-- ⟨1, 0, 0, -784, -8515⟩
-- E : y^2 + xy = x^3 - 784x - 8515

def foo (p : ℕ) (h : Fact p.Prime := by decide) := (Finset.univ.filter
  fun xy : (ZMod p) × (ZMod p) ↦ xy.2 ^ 2 + xy.1 * xy.2 = xy.1 ^ 3 - 784 * xy.1 - 8515).card

#eval foo 29

theorem bar : foo 29 = 31 := by decide
