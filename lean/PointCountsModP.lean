import Mathlib
open Polynomial

set_option maxRecDepth 10000

-- Define Weierstrass curve E : y^2 + a₁xy + a₃y = x^3 + a₂x^2 + a₄x + a₆ over ℤ

def E : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -784
  a₆ := -8515

-- Compute the number of points on E over the finite field 𝔽ₚ using two different methods

def compute_points_mod_p_sum (p : ℕ) (h : Fact p.Prime) : ℤ :=
  ∑ x ∈ (Finset.univ : Finset (ZMod p)),
  {y ∈ (Finset.univ : Finset (ZMod p))
  | y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x^2 + E.a₄ * x + E.a₆}.card

def compute_points_mod_p'_sum (p : ℕ) (h : Fact p.Prime) : ℤ :=
  ∑ x ∈ (Finset.univ : Finset (ZMod p)),
      (legendreSym p
        ((E.a₁ * x.val + E.a₃) ^ 2
        + 4 * (x.val ^ 3 + E.a₂ * x.val ^ 2 + E.a₄ * x.val + E.a₆))
        + 1)

#eval compute_points_mod_p_sum  29 (by decide)
#eval compute_points_mod_p'_sum 29 (by decide)


/-- **Counting roots of a quadratic via its discriminant.**  Over a finite field `F` in which
`2 ≠ 0`, completing the square — `y ↦ 2a·y + b` — is a bijection between the roots of
`a·y² + b·y + c` and the square roots of the discriminant `b² - 4ac`, so the two solution sets
have the same cardinality. -/
theorem card_quadratic_roots_eq_card_sqrts_discrim {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    {y : F | a * y ^ 2 + b * y + c = 0}.toFinset.card
      = {z : F | z ^ 2 = discrim a b c}.toFinset.card := by
  haveI : NeZero (2 : F) := ⟨h2⟩
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  refine Finset.card_nbij' (fun y => 2 * a * y + b) (fun z => (z - b) / (2 * a)) ?_ ?_ ?_ ?_
  · -- a root `y` yields the square root `2a·y + b` of the discriminant
    intro y hy
    simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf_eq] at hy ⊢
    exact ((quadratic_eq_zero_iff_discrim_eq_sq ha y).mp (by linear_combination hy)).symm
  · -- a square root `z` yields back the root `(z - b) / 2a`
    intro z hz
    simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf_eq] at hz ⊢
    have hzz : 2 * a * ((z - b) / (2 * a)) + b = z := by rw [mul_div_cancel₀ _ h2a]; ring
    have key := (quadratic_eq_zero_iff_discrim_eq_sq ha ((z - b) / (2 * a))).mpr
      (by rw [hzz, hz])
    linear_combination key
  · -- the two maps are mutually inverse
    intro y _
    field_simp
    ring
  · intro z _
    field_simp
    ring

theorem compute_points_methods_equivalent (p : ℕ) (h : Fact p.Prime)
  (h2 : p ≠ 2) :
  compute_points_mod_p_sum p h = compute_points_mod_p'_sum p h := by
  rw [compute_points_mod_p_sum, compute_points_mod_p'_sum]
  -- Reduce to the per-x identity  #{y : Weierstrass eqn} = legendreSym p (discriminant) + 1.
  apply Finset.sum_congr rfl
  intro x _
  -- `p ≠ 2` enters only here and through `legendreSym.card_sqrts`.
  have two_ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr h2)
  rw [← legendreSym.card_sqrts p h2
        ((E.a₁ * ↑x.val + E.a₃) ^ 2 + 4 * (↑x.val ^ 3 + E.a₂ * ↑x.val ^ 2 + E.a₄ * ↑x.val + E.a₆)),
      Nat.cast_inj]
  -- The fibre over `x` is the root set of the monic quadratic  y² + (a₁x + a₃)y - RHS  in `y`.
  have hquad : {y ∈ (Finset.univ : Finset (ZMod p)) |
        y ^ 2 + ↑E.a₁ * x * y + ↑E.a₃ * y = x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆}
      = {y : ZMod p | 1 * y ^ 2 + (↑E.a₁ * x + ↑E.a₃) * y
          + -(x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆) = 0}.toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_setOf_eq]
    constructor <;> intro hy <;> linear_combination hy
  rw [hquad, card_quadratic_roots_eq_card_sqrts_discrim two_ne one_ne_zero]
  -- The quadratic's discriminant is the cast of the integer discriminant of the curve at `x`.
  have hdisc : discrim (1 : ZMod p) (↑E.a₁ * x + ↑E.a₃)
        (-(x ^ 3 + ↑E.a₂ * x ^ 2 + ↑E.a₄ * x + ↑E.a₆))
      = (((E.a₁ * ↑x.val + E.a₃) ^ 2
          + 4 * (↑x.val ^ 3 + E.a₂ * ↑x.val ^ 2 + E.a₄ * ↑x.val + E.a₆) : ℤ) : ZMod p) := by
    rw [discrim]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [hdisc]





-- Old counting points mod p
def compute_points_mod_p (p : ℕ) [NeZero p] : ℤ :=
  (((Finset.univ : Finset ((ZMod p) × (ZMod p))).filter fun ⟨x, y⟩ =>
    y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x^2 + E.a₄ * x + E.a₆).card : ℤ)

-- Old counting points mod p'
def compute_points_mod_p' (p : ℕ) (h : Fact p.Prime) : ℤ :=
  ((Finset.univ : Finset (ZMod p)).val.map fun x : ZMod p =>
    legendreSym p
      ((E.a₁ * x.val + E.a₃) ^ 2 + 4 * (x.val ^ 3 +
        E.a₂ * x.val ^ 2 + E.a₄ * x.val + E.a₆)) + 1).sum





-- Local Euler factor at a good prime p
noncomputable def L_factor_at_p_good (p : ℕ) (h : Fact p.Prime) : ℤ[X] :=
  let a_p := compute_points_mod_p_sum p h
  1 - (p - a_p) • X + (p : ℤ) • X ^ 2

-- Reduction type checks at a prime p

def p_is_good (p : ℕ) (h : Fact p.Prime) : Bool :=
  decide (¬ ((p : ℤ) ∣ E.Δ))

def p_is_split_multiplicative (p : ℕ) (h : Fact p.Prime) : Bool :=
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ E.c₄) ∧ (legendreSym p (-E.c₆) = 1)

def p_is_non_split_multiplicative (p : ℕ) (h : Fact p.Prime) : Bool :=
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ E.c₄) ∧ (legendreSym p (-E.c₆) = -1)

def p_is_additive (p : ℕ) (h : Fact p.Prime) : Bool :=
  decide ((p : ℤ) ∣ E.Δ) ∧ (p : ℤ) ∣ E.c₄

#eval p_is_good 29 (by decide)
#eval p_is_split_multiplicative 29 (by decide)
#eval p_is_non_split_multiplicative 29 (by decide)
#eval p_is_additive 29 (by decide)

theorem foo1 : p_is_good 29 (by decide) ∧ L_factor_at_p_good 29 (by decide) = 1 + 2 • X + 29 • X ^ 2 := by
  constructor
  · decide
  · rw [L_factor_at_p_good, sub_eq_add_neg, ← neg_zsmul]
    rfl
