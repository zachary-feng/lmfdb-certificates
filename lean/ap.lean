import Mathlib

def p := 7
instance : Fact (Nat.Prime 7) := by decide

def E : WeierstrassCurve ℤ := ⟨1,0,0,-44091,-9992106⟩
noncomputable def E_Q : WeierstrassCurve ℚ_[7] := ⟨1,0,0,-44091,-9992106⟩

#check 1+1

#check (30: ZMod 7)
#check (37: ZMod 7)

def x := (30: ZMod 7)
def y := (37: ZMod 7)

theorem h : x = y := by
  decide


def E_3 : WeierstrassCurve ℤ := ⟨1,0,0,-44091,-9992106⟩
