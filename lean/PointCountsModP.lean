import Mathlib

-- Reduction mod p
def p : ℕ := 5

instance : Fact p.Prime := by decide

-- Isogeny class: 21.a
-- Weierstrass curve: 21.a1
noncomputable def E : WeierstrassCurve (ℚ_[p]) := ⟨1,0,0,-784,-8515⟩

noncomputable def E_mod_p : WeierstrassCurve (ZMod p) := ⟨1, 0, 0, -784, -8515⟩


-- try p^2 points, i++, whenever get a solution

instance : DecidableEq (ZMod p × ZMod p) := by infer_instance

open Finset

def foo (p : ℕ) (h : Fact p.Prime := by decide) := (Finset.univ.filter
  fun xy : (ZMod p) × (ZMod p) ↦ xy.2 ^ 2 + xy.1 * xy.2 = xy.1 ^ 3 - 784 * xy.1 - 8515).card

#eval foo 29

theorem bar : foo 29 = 31 := by decide
