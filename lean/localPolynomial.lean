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

instance W_good : HasGoodReduction ℤ_[5] W := ⟨val_Δ⟩

/-! ### Piece 5: point count of an elliptic curve over a finite field, via `pointEquiv` -/
theorem card_point_eq (F : Type) [Field F] [Finite F] (V : WeierstrassCurve F)
    [V.IsElliptic] :
    Nat.card V.toAffine.Point = Nat.card {xy : F × F // V.toAffine.Equation xy.1 xy.2} + 1 := by
  rw [Nat.card_congr V.toAffine.pointEquiv]
  simp [WithZero]

/-! ### Piece 6: transfer to the chosen minimal model `W' = W.minimal ℤ_[5]` -/

/-- The change of variables mathlib chose. We can name it, but never inspect it. -/
noncomputable abbrev Cmin : VariableChange ℚ_[5] := (W.exists_isMinimal ℤ_[5]).choose

lemma minimal_eq : W.minimal ℤ_[5] = Cmin • W := rfl

lemma inv_Cmin_smul : Cmin⁻¹ • W.minimal ℤ_[5] = W := by rw [minimal_eq, inv_smul_smul]

/-- 6a. `W'` has good reduction. `W = Cmin⁻¹ • W'` is an integral model with `v(Δ) = 1`, and `W'`
is minimal, so `MaximalFor` gives `v(Δ W') ≥ v(Δ W) = 1`; the other inequality always holds. -/
lemma val_Δ_minimal : valuation ℚ_[5] (maximalIdeal ℤ_[5]) (W.minimal ℤ_[5]).Δ = 1 := by
  have hint : IsIntegral ℤ_[5] (Cmin⁻¹ • W.minimal ℤ_[5]) := by rw [inv_Cmin_smul]; exact W_int
  have hmax := (IsMinimal.val_Δ_maximal (R := ℤ_[5]) (W := W.minimal ℤ_[5])).2 hint
  simp only [one_smul, inv_Cmin_smul] at hmax
  -- `v(Δ W) = 1` is the top value, so the premise of `hmax` is automatic
  have htop : valuation_Δ_aux ℤ_[5] (W.minimal ℤ_[5]) ≤ valuation_Δ_aux ℤ_[5] W := by
    rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral ℤ_[5] W, val_Δ]
    exact (valuation_Δ_aux ℤ_[5] _).2
  have h := Subtype.coe_le_coe.mpr (hmax htop)
  rw [valuation_Δ_aux_eq_of_isIntegral ℤ_[5] W, val_Δ,
    valuation_Δ_aux_eq_of_isIntegral ℤ_[5] (W.minimal ℤ_[5])] at h
  refine le_antisymm ?_ h
  rw [← valuation_Δ_aux_eq_of_isIntegral ℤ_[5]]
  exact (valuation_Δ_aux ℤ_[5] _).2

instance W'_good : HasGoodReduction ℤ_[5] (W.minimal ℤ_[5]) := ⟨val_Δ_minimal⟩

/-- 6f (i). The affine point count of `E` over `ZMod 5`, by brute force. -/
lemma count_affine_zmod5 :
    Nat.card {xy : ZMod 5 × ZMod 5 // xy.2 ^ 2 + xy.1 * xy.2 = xy.1 ^ 3 - 2 * xy.1 + 1} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- 6f (ii). The integral model mathlib extracts from `W` is `E` itself (as a curve over `ℤ_[5]`),
because `algebraMap ℤ_[5] ℚ_[5]` is injective. -/
lemma integralModel_W : integralModel ℤ_[5] W = E.map (Int.castRingHom ℤ_[5]) := by
  apply map_injective (IsFractionRing.injective ℤ_[5] ℚ_[5])
  have h := baseChange_integralModel_eq ℤ_[5] W
  simp only [WeierstrassCurve.baseChange] at h ⊢
  rw [h, WeierstrassCurve.map_map]
  exact congrArg _ (RingHom.ext_int _ _)

/-- 6f (iii). Hence the reduction of `W` is `E` over the residue field. -/
lemma reduction_W :
    W.reduction ℤ_[5] = E.map (Int.castRingHom (IsLocalRing.ResidueField ℤ_[5])) := by
  rw [WeierstrassCurve.reduction, integralModel_W, WeierstrassCurve.map_map]
  exact congrArg _ (RingHom.ext_int _ _)

/-- 6f (iv). The affine point count of an integer curve over a field only depends on the field
up to isomorphism. -/
lemma card_equation_map {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') (V : WeierstrassCurve ℤ) :
    Nat.card {xy : F × F // (V.map (Int.castRingHom F)).toAffine.Equation xy.1 xy.2}
      = Nat.card {xy : F' × F' // (V.map (Int.castRingHom F')).toAffine.Equation xy.1 xy.2} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) fun xy => ?_)
  simp only [Affine.equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← e.injective.eq_iff]
  simp

instance : Finite (IsLocalRing.ResidueField ℤ_[5]) :=
  Finite.of_equiv _ PadicInt.residueField.symm.toEquiv

instance : (W.reduction ℤ_[5]).IsElliptic :=
  (hasGoodReduction_iff_isElliptic_reduction ℤ_[5]).mp W_good

/-- 6f. `W` has 9 points mod 5: 8 affine ones and the point at infinity. -/
lemma card_reduction_W : Nat.card (W.reduction ℤ_[5]).toAffine.Point = 9 := by
  rw [card_point_eq, reduction_W, card_equation_map PadicInt.residueField E]
  have key : ∀ xy : ZMod 5 × ZMod 5,
      (E.map (Int.castRingHom (ZMod 5))).toAffine.Equation xy.1 xy.2 ↔
        xy.2 ^ 2 + xy.1 * xy.2 = xy.1 ^ 3 - 2 * xy.1 + 1 := by
    intro xy
    simp only [Affine.equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, E, eq_intCast]
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), count_affine_zmod5]

/-- 6e (i). A change of variables `(u, r, s, t)` moves a point `(x, y)` of `D • V` to the point
`(u²x + r, u³y + u²sx + t)` of `V`. -/
lemma equation_variableChange_iff {F : Type} [Field F] (V : WeierstrassCurve F)
    (D : VariableChange F) (x y : F) :
    (D • V).toAffine.Equation x y ↔
      V.toAffine.Equation (D.u ^ 2 * x + D.r) (D.u ^ 3 * y + D.u ^ 2 * D.s * x + D.t) := by
  simp only [Affine.equation_iff, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  constructor <;> intro h <;> field_simp at h ⊢ <;> linear_combination h

/-- 6e (ii). That map is a bijection of the affine plane. -/
def affineEquiv {F : Type} [Field F] (D : VariableChange F) : F × F ≃ F × F where
  toFun xy := (D.u ^ 2 * xy.1 + D.r, D.u ^ 3 * xy.2 + D.u ^ 2 * D.s * xy.1 + D.t)
  invFun xy := (D.u⁻¹ ^ 2 * (xy.1 - D.r), D.u⁻¹ ^ 3 * (xy.2 - D.s * (xy.1 - D.r) - D.t))
  left_inv xy := by ext <;> simp [Units.val_inv_eq_inv_val] <;> field_simp <;> ring
  right_inv xy := by ext <;> simp [Units.val_inv_eq_inv_val] <;> field_simp <;> ring

/-- 6e. Over a field, a change of variables does not change the number of points. -/
lemma card_point_variableChange {F : Type} [Field F] [Finite F] (V : WeierstrassCurve F)
    [V.IsElliptic] (D : VariableChange F) :
    Nat.card (D • V).toAffine.Point = Nat.card V.toAffine.Point := by
  rw [card_point_eq, card_point_eq, Nat.card_congr (Equiv.subtypeEquiv
    (p := fun xy => (D • V).toAffine.Equation xy.1 xy.2)
    (q := fun xy => V.toAffine.Equation xy.1 xy.2)
    (affineEquiv D) fun xy => equation_variableChange_iff V D xy.1 xy.2)]

/-! ### 6b–6d: the chosen change of variables is integral, so it reduces mod 5 -/

/-- 6b (i). The discriminant of the chosen model is a unit of `ℤ_[5]` (it has valuation 1). -/
lemma isUnit_Δ_minimal : IsUnit (integralModel ℤ_[5] (W.minimal ℤ_[5])).Δ := by
  have h := val_Δ_minimal
  rw [← integralModel_Δ_eq ℤ_[5] (W.minimal ℤ_[5]), valuation_eq_one_iff_notMem] at h
  exact IsLocalRing.notMem_maximalIdeal.mp h

/-- 6b (ii). `Cmin.u ^ 12 = Δ(W) / Δ(W')` is the image of a unit of `ℤ_[5]`. -/
lemma u_pow_twelve : ∃ w : ℤ_[5]ˣ, algebraMap ℤ_[5] ℚ_[5] w = (Cmin.u : ℚ_[5]) ^ 12 := by
  refine ⟨unit61.unit * isUnit_Δ_minimal.unit⁻¹, ?_⟩
  have hΔ' : algebraMap ℤ_[5] ℚ_[5] (integralModel ℤ_[5] (W.minimal ℤ_[5])).Δ
      = (Cmin.u⁻¹ : ℚ_[5]ˣ) ^ 12 * W.Δ := by
    rw [integralModel_Δ_eq, minimal_eq, variableChange_Δ]
  simp only [Units.val_mul, map_mul, map_units_inv, IsUnit.unit_spec, hΔ', W_Δ,
    Units.val_inv_eq_inv_val, map_neg, map_ofNat]
  field_simp

/-- 6b (iii). `ℤ_[5]` is integrally closed and `Cmin.u ^ 12` is a unit of it, so `Cmin.u` is too. -/
lemma exists_unit_u : ∃ u : ℤ_[5]ˣ, algebraMap ℤ_[5] ℚ_[5] u = Cmin.u := by
  obtain ⟨w, hw⟩ := u_pow_twelve
  have hint : _root_.IsIntegral ℤ_[5] (Cmin.u : ℚ_[5]) :=
    ⟨X ^ 12 - C (w : ℤ_[5]), by monicity!, by simp [hw]⟩
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hr12 : r ^ 12 = w := by
    apply IsFractionRing.injective ℤ_[5] ℚ_[5]
    rw [map_pow, hr, hw]
  have hu : IsUnit r := (isUnit_pow_iff (by norm_num : (12 : ℕ) ≠ 0)).mp (hr12 ▸ w.isUnit)
  exact ⟨hu.unit, by simp [hr]⟩

/-- 6c. Descent (Riccardo Brasca's lemma): `Cmin` comes from a change of variables over `ℤ_[5]`. -/
lemma exists_CR : ∃ CR : VariableChange ℤ_[5], CR.baseChange ℚ_[5] = Cmin := by
  obtain ⟨u, hu⟩ := exists_unit_u
  exact variableChange_integral_of_u_integral (W := W) (W' := W.minimal ℤ_[5]) minimal_eq.symm hu

/-- 6d. Hence the reduction of `W'` is a change of variables of the reduction of `W`. -/
lemma reduction_minimal : ∃ D : VariableChange (IsLocalRing.ResidueField ℤ_[5]),
    (W.minimal ℤ_[5]).reduction ℤ_[5] = D • W.reduction ℤ_[5] := by
  obtain ⟨CR, hCR⟩ := exists_CR
  refine ⟨CR.map (IsLocalRing.residue ℤ_[5]), ?_⟩
  have hmodel : integralModel ℤ_[5] (W.minimal ℤ_[5]) = CR • integralModel ℤ_[5] W := by
    apply map_injective (IsFractionRing.injective ℤ_[5] ℚ_[5])
    beta_reduce
    rw [← map_variableChange]
    have h1 : (integralModel ℤ_[5] (W.minimal ℤ_[5])).map (algebraMap ℤ_[5] ℚ_[5])
        = W.minimal ℤ_[5] := baseChange_integralModel_eq ℤ_[5] _
    have h2 : (integralModel ℤ_[5] W).map (algebraMap ℤ_[5] ℚ_[5]) = W :=
      baseChange_integralModel_eq ℤ_[5] _
    rw [h1, h2, minimal_eq, ← hCR]
    rfl
  rw [WeierstrassCurve.reduction, WeierstrassCurve.reduction, hmodel, ← map_variableChange]

/-! ### The two facts about `W' = W.minimal ℤ_[5]` that `localPolynomial` needs
`localPolynomial` is stated for `W.minimal ℤ_[5]`, which is `(exists_isMinimal ..).choose • W`.
Mathlib has no lemma relating `W.minimal R` back to `W` when `W` is already minimal; Piece 6
above supplies the transfer for this curve. -/
theorem hasGoodReduction_minimal : HasGoodReduction ℤ_[5] (W.minimal ℤ_[5]) := W'_good

theorem card_point_minimal :
    Nat.card ((W.minimal ℤ_[5]).reduction ℤ_[5]).toAffine.Point = 9 := by
  obtain ⟨D, hD⟩ := reduction_minimal
  rw [hD, card_point_variableChange, card_reduction_W]


#check localPolynomial
#check W.minimal ℤ_[5]

/-- The certificate: `hasGoodReduction_minimal` picks the good-reduction branch of the `if`,
`card_point_minimal` supplies `|W'(κ)| = 9`, and `simp` does the arithmetic `5 + 1 - 9 = -3`. -/
theorem localPolynomial_E_5 : localPolynomial ℤ_[5] W = 1 + C 3 * X + C 5 * X ^ 2 := by
  simp [localPolynomial, hasGoodReduction_minimal, card_residueField, card_point_minimal]
