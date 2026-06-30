import Mathlib

-- Isogeny class: 21.a
-- Weierstrass curve: 21.a1
-- ⟨1, 0, 0, -784, -8515⟩
-- E : y^2 + xy = x^3 - 784x - 8515




def foo (p : ℕ) (h : Fact p.Prime := by decide) := (Finset.univ.filter
  fun xy : (ZMod p) × (ZMod p) ↦ xy.2 ^ 2 + xy.1 * xy.2 = xy.1 ^ 3 - 784 * xy.1 - 8515).card

def foo2 (p : ℕ) (h : Fact p.Prime := by decide) (a1 a2 a3 a4 a6 : ℤ) := (Finset.univ.filter
  fun xy : (ZMod p) × (ZMod p) ↦ xy.2 ^ 2 + a1 * xy.1 * xy.2 + a3 * xy.2 = xy.1 ^ 3 + a2 * xy.1^2 + a4 * xy.1 + a6).card

def foo3 (p : ℕ) (h : Fact p.Prime := by decide) (a1 a2 a3 a4 a6 : ℤ) := (Finset.univ.filter
  fun xy : (ZMod p) × (ZMod p) ↦
  let x := xy.1
  let y:= xy.2
  y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6).card

#eval foo 29

theorem bar : foo 29 = 31 := by decide
