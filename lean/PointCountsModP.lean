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

def compute_points_mod_p_sum (p : ℕ) (h : Fact p.Prime) : ℕ :=
  ∑ x : (ZMod p),
  ({y : ZMod p
  | y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x^2 + E.a₄ * x + E.a₆} : Finset _).card

def compute_points_mod_p'_sum (p : ℕ) (h : Fact p.Prime) : ℤ :=
  ∑ x : ZMod p,
      (legendreSym p
        ((E.a₁ * x.val + E.a₃) ^ 2
        + 4 * (x.val ^ 3 + E.a₂ * x.val ^ 2 + E.a₄ * x.val + E.a₆))
        + 1)

-- set_option trace.profiler true
-- set_option maxRecDepth 300000
-- #eval compute_points_mod_p'_sum 641 (by decide)
-- #eval compute_points_mod_p_sum 641 (by decide)


/-- **Counting roots of a quadratic via its discriminant.**  Over a finite field `F` in which
`2 ≠ 0`, completing the square — `y ↦ 2a·y + b` — is a bijection between the roots of
`a·y² + b·y + c` and the square roots of the discriminant `b² - 4ac`, so the two solution sets
have the same cardinality. -/
theorem card_quadratic_roots_eq_card_sqrts_discrim {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    ({y : F | a * y ^ 2 + b * y + c = 0} : Finset F).card
      = ({z : F | z ^ 2 = discrim a b c} : Finset F).card := by
  haveI : NeZero (2 : F) := ⟨h2⟩
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  refine Finset.card_nbij' (fun y => 2 * a * y + b) (fun z => (z - b) / (2 * a)) ?_ ?_ ?_ ?_
  · -- a root `y` yields the square root `2a·y + b` of the discriminant
    intro y hy
    simp [discrim]
    grind
  · -- a square root `z` yields back the root `(z - b) / 2a`
    intro z hz
    simp [discrim] at hz
    simp
    field_simp
    grind
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
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  rw [← legendreSym.card_sqrts _ h2]
  have two_ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr h2)
  norm_cast
  convert card_quadratic_roots_eq_card_sqrts_discrim two_ne one_ne_zero
      (E.a₁ * x + E.a₃) (-(x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)) using 2
  · grind
  · unfold discrim
    simp [Set.toFinset_setOf]
    grind

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
  let N_p := compute_points_mod_p_sum p h
  1 - C (p - N_p : ℤ) * X + C (p : ℤ) * X ^ 2

#print L_factor_at_p_good

-- Reduction type checks at a prime p

def p_is_good (p : ℕ) (_ : Fact p.Prime) := (¬ ((p : ℤ) ∣ E.Δ))
  deriving Decidable

def p_is_split_multiplicative (p : ℕ) (h : Fact p.Prime) :=
  ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ E.c₄) ∧ (legendreSym p (-E.c₆) = 1)
  deriving Decidable

def p_is_non_split_multiplicative (p : ℕ) (h : Fact p.Prime) :=
  ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ E.c₄) ∧ (legendreSym p (-E.c₆) = -1)
  deriving Decidable

def p_is_additive (p : ℕ) (_ : Fact p.Prime) :=
  ((p : ℤ) ∣ E.Δ) ∧ (p : ℤ) ∣ E.c₄
  deriving Decidable

#eval p_is_good 29 (by decide)
#eval p_is_split_multiplicative 29 (by decide)
#eval p_is_non_split_multiplicative 29 (by decide)
#eval p_is_additive 29 (by decide)

theorem foo1 : p_is_good 29 (by decide) ∧ L_factor_at_p_good 29 (by decide)
= 1 + C (2 : ℤ) * X + C (29 : ℤ) * X ^ 2 := by
  constructor
  · decide
  · unfold L_factor_at_p_good
    polynomial_nf
    rfl
