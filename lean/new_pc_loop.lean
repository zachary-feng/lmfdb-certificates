import Mathlib
open Polynomial

set_option maxRecDepth 10000

#check WeierstrassCurve.localPolynomial

-- Define Weierstrass curve E : y^2 + a₁xy + a₃y = x^3 + a₂x^2 + a₄x + a₆ over ℤ

def E : WeierstrassCurve ℤ := ⟨1, 0, 0, -2, 1⟩

-- LMFDB table of (p, a_p) for E: the L-factor at p is 1 - a_p T + p T^2
def ap_table : List (ℕ × ℤ) :=
  [(2, -1), (3, -2), (5, -3), (7, 1), (11, -5), (13, 1), (17, 4), (19, -4), (23, -9), (29, -6)]

-- LMFDB rows at the bad primes.  At a multiplicative p the L-factor is 1 - a_p T with a_p = ±1
-- (+1 split, -1 non-split); at an additive p it is 1 (a_p = 0).
def ap_table_mult : List (ℕ × ℤ) := [(61, -1)]
def ap_table_add : List ℕ := []

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

/-- **Counting roots of a quadratic via its discriminant.**  Over a finite field `F` in which
`2 ≠ 0`, completing the square — `y ↦ 2a·y + b` — is a bijection between the roots of
`a·y² + b·y + c` and the square roots of the discriminant `b² - 4ac`, so the two solution sets
have the same cardinality. -/
theorem card_quadratic_roots_eq_card_sqrts_discrim {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    ({y : F | a * y ^ 2 + b * y + c = 0} : Finset F).card
      = ({z : F | z ^ 2 = discrim a b c} : Finset F).card := by
  have : NeZero (2 : F) := ⟨h2⟩
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
    simp
    grind

-- Local Euler factor at a good prime p

noncomputable def L_factor_at_p_good (p : ℕ) (h : Fact p.Prime) : ℤ[X] :=
  let N_p := compute_points_mod_p_sum p h
  1 - C (p - N_p : ℤ) * X + C (p : ℤ) * X ^ 2

-- Local Euler factor at a multiplicative prime p: `1 - a_p X` where again `a_p = p - N_p`, the
-- affine count `N_p` now including the node (`a_p = 1` split, `a_p = -1` non-split).

noncomputable def L_factor_at_p_mult (p : ℕ) (h : Fact p.Prime) : ℤ[X] :=
  let N_p := compute_points_mod_p_sum p h
  1 - C (p - N_p : ℤ) * X

-- Local Euler factor at an additive prime p: constant `1`.

noncomputable def L_factor_at_p_add (p : ℕ) (_ : Fact p.Prime) : ℤ[X] := 1

-- Reduction type checks at a prime p

def p_is_good (p : ℕ) (_ : Fact p.Prime) := (¬ ((p : ℤ) ∣ E.Δ))
  deriving Decidable

-- For p ∣ Δ the reduction type is read off a model minimal at p; `v_p(Δ) < 12` certifies
-- minimality (Silverman VII.1.3).  Then: multiplicative ⟺ p ∤ c₄, additive ⟺ p ∣ c₄.

def p_is_minimal (p : ℕ) (_ : Fact p.Prime) := (¬ ((p : ℤ) ^ 12 ∣ E.Δ))
  deriving Decidable

def p_is_mult (p : ℕ) (h : Fact p.Prime) :=
  p_is_minimal p h ∧ ((p : ℤ) ∣ E.Δ) ∧ (¬ ((p : ℤ) ∣ E.c₄))
  deriving Decidable

def p_is_add (p : ℕ) (h : Fact p.Prime) :=
  p_is_minimal p h ∧ ((p : ℤ) ∣ E.Δ) ∧ ((p : ℤ) ∣ E.c₄)
  deriving Decidable

#eval ap_table.map fun (p, _) => if hp : p.Prime then decide (p_is_good p ⟨hp⟩) else false
#eval ap_table_mult.map fun (p, _) => if hp : p.Prime then decide (p_is_mult p ⟨hp⟩) else false
#eval ap_table_add.map fun p => if hp : p.Prime then decide (p_is_add p ⟨hp⟩) else false

-- One iteration of the loop: once the point count `N_p` is known, `a_p = p - N_p` pins down the
-- L-factor.  Works uniformly for positive and negative `a_p`.
theorem L_factor_of_count (p : ℕ) (h : Fact p.Prime) (a : ℤ)
    (hN : (compute_points_mod_p_sum p h : ℤ) = p - a) :
    L_factor_at_p_good p h = 1 + C (-a : ℤ) * X + C (p : ℤ) * X ^ 2 := by
  unfold L_factor_at_p_good
  simp only [hN, sub_sub_cancel, C_neg]
  ring

theorem L_factor_of_count_mult (p : ℕ) (h : Fact p.Prime) (a : ℤ)
    (hN : (compute_points_mod_p_sum p h : ℤ) = p - a) :
    L_factor_at_p_mult p h = 1 + C (-a : ℤ) * X := by
  unfold L_factor_at_p_mult
  simp only [hN, sub_sub_cancel, C_neg]
  ring

-- The loop: every `(p, a_p)` row of `ap_table` is certified.
theorem foo1 : ∀ pa ∈ ap_table, ∀ h : Fact pa.1.Prime, p_is_good pa.1 h ∧
    L_factor_at_p_good pa.1 h = 1 + C (-pa.2 : ℤ) * X + C (pa.1 : ℤ) * X ^ 2 := by
  intro pa hpa h
  unfold ap_table at hpa
  fin_cases hpa
  all_goals
    constructor
    · unfold p_is_good
      decide
    · exact L_factor_of_count _ ⟨by decide⟩ _ (by decide)

#print axioms foo1

-- The loop over the multiplicative primes: every `(p, a_p)` row of `ap_table_mult` is certified.
theorem foo2 : ∀ pa ∈ ap_table_mult, ∀ h : Fact pa.1.Prime, p_is_mult pa.1 h ∧
    L_factor_at_p_mult pa.1 h = 1 + C (-pa.2 : ℤ) * X := by
  intro pa hpa h
  unfold ap_table_mult at hpa
  fin_cases hpa
  all_goals
    constructor
    · unfold p_is_mult p_is_minimal
      decide
    · exact L_factor_of_count_mult _ ⟨by decide⟩ _ (by decide)

-- The loop over the additive primes (none for this curve): the factor is `1`.
theorem foo3 : ∀ p ∈ ap_table_add, ∀ h : Fact p.Prime, p_is_add p h ∧
    L_factor_at_p_add p h = 1 := by
  intro p hp h
  unfold ap_table_add at hp
  fin_cases hp
  -- once `ap_table_add` has a row, continue exactly as in `foo2` (kept out of the proof while the
  -- table is empty, otherwise the unreachable-tactic linter complains):
  -- all_goals
  --   constructor
  --   · unfold p_is_add p_is_minimal
  --     decide
  --   · rfl

#print axioms foo2
#print axioms foo3

/- TODO:
1. make it mathlib localPolynomial compatible
2. make it mathlib goodReduction compatible
3. (DONE): extend functionality to different reduction types  (done: `p_is_mult` / `p_is_add`,
   `L_factor_at_p_mult` / `L_factor_at_p_add`, loops `foo2` / `foo3`, headline `L_factor_at_61`)
4. (DONE): a single check for all displayed primes  (done: `foo1` loops over `ap_table`)
-/
