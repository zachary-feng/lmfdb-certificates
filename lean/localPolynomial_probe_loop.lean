import Mathlib

/-!
# Connecting `WeierstrassCurve.localPolynomial` to the workshop certificate

Probe: how much of `localPolynomial ℤ_[5] (E ⁄ ℚ_[5]) = 1 + 3 X + 5 X²` can be proved with the
mathlib API as of 2026-09-03 (Mathlib master, Lean v4.34.0-rc2).
-/

open Polynomial WeierstrassCurve IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def E : WeierstrassCurve ℤ := ⟨1, 0, 0, -2, 1⟩

/-- `E` viewed over the 5-adic numbers: the input `localPolynomial` actually wants. -/
noncomputable abbrev W : WeierstrassCurve ℚ_[5] := E.baseChange ℚ_[5]

-- The term elaborates; it is `noncomputable` (choice of minimal model, `Nat.card`, classical `if`).
#check (localPolynomial ℤ_[5] W : ℤ[X])

lemma E_Δ : E.Δ = -61 := by decide

lemma W_Δ : W.Δ = -61 := by
  simp [W, WeierstrassCurve.baseChange, map_Δ, E_Δ]

/-! ### Piece 1: the residue field has 5 elements -/
lemma card_residueField : Nat.card (IsLocalRing.ResidueField ℤ_[5]) = 5 := by
  rw [Nat.card_congr (PadicInt.residueField (p := 5)).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ### Piece 2: `W` is integral over `ℤ_[5]` -/
instance W_int : IsIntegral ℤ_[5] W := by
  refine isIntegral_of_exists_lift (R := ℤ_[5]) ?_ ?_ ?_ ?_ ?_
  · exact ⟨1, by simp [W, E, WeierstrassCurve.baseChange]⟩
  · exact ⟨0, by simp [W, E, WeierstrassCurve.baseChange]⟩
  · exact ⟨0, by simp [W, E, WeierstrassCurve.baseChange]⟩
  · exact ⟨-2, by simp [W, E, WeierstrassCurve.baseChange]; norm_cast⟩
  · exact ⟨1, by simp [W, E, WeierstrassCurve.baseChange]⟩

/-! ### Piece 3: `Δ = -61` is a 5-adic unit, so `v(Δ) = 1` -/
lemma unit61 : IsUnit (-61 : ℤ_[5]) := by
  rw [PadicInt.isUnit_iff]
  have h1 : ‖(-61 : ℤ_[5])‖ ≤ 1 := PadicInt.norm_le_one _
  have h2 : ¬ ‖((-61 : ℤ) : ℤ_[5])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]; norm_num
  push_cast at h2
  exact le_antisymm h1 (not_lt.mp h2)

lemma val_Δ : valuation ℚ_[5] (maximalIdeal ℤ_[5]) W.Δ = 1 := by
  rw [W_Δ]
  have : (-61 : ℚ_[5]) = algebraMap ℤ_[5] ℚ_[5] (-61) := by push_cast; rfl
  rw [this, valuation_eq_one_iff_notMem]
  exact IsLocalRing.notMem_maximalIdeal.mpr unit61

/-! ### Piece 4: `W` is minimal and has good reduction.
Since `v(Δ) = 1` is the largest value the valuation of an integral discriminant can take,
maximality is automatic. -/
instance W_min : IsMinimal ℤ_[5] W := by
  refine ⟨⟨?_, ?_⟩⟩
  · simpa using W_int
  · intro j hj _
    simp only [one_smul]
    rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral ℤ_[5] W, val_Δ]
    exact (valuation_Δ_aux ℤ_[5] (j • W)).2

#check HasGoodReduction
instance W_good : HasGoodReduction ℤ_[5] W := ⟨val_Δ⟩

/-! ### Piece 5: point count of an elliptic curve over a finite field, via `pointEquiv` -/
theorem card_point_eq (F : Type) [Field F] [Fintype F] (V : WeierstrassCurve F)
    [V.IsElliptic] :
    Nat.card V.toAffine.Point = Nat.card {xy : F × F // V.toAffine.Equation xy.1 xy.2} + 1 := by
  rw [Nat.card_congr V.toAffine.pointEquiv]
  simp [WithZero]


#check W.minimal ℤ_[5]

/-! ### The blocker
`localPolynomial` is stated for `W.minimal ℤ_[5]`, which is `(exists_isMinimal ..).choose • W`.
Mathlib has no lemma relating `W.minimal R` back to `W` when `W` is already minimal, nor any
lemma that reduction / point counts are invariant under an integral change of variables.
Both `sorry`s below need that missing infrastructure. -/
example : HasGoodReduction ℤ_[5] (W.minimal ℤ_[5]) := by
  sorry

example : Nat.card ((W.minimal ℤ_[5]).reduction ℤ_[5]).toAffine.Point = 9 := by
  sorry

/-- What the final certificate would look like once the blocker is resolved. -/
example : localPolynomial ℤ_[5] W = 1 + C 3 * X + C 5 * X ^ 2 := by
  sorry
