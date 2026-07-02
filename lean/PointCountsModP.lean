import Mathlib
open Polynomial

def compute_points_mod_p (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  (Finset.univ.filter
    fun xy : (ZMod p) × (ZMod p) ↦
      letI x := xy.1
      letI y := xy.2
    y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6).card



def compute_points_mod_p' (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  ((Finset.univ : Finset (ZMod p)).val.map
    (fun x : ZMod p ↦
      legendreSym p
        ((a1 * x.val + a3) ^ 2
          + 4 * (x.val ^ 3 + a2 * x.val ^ 2 + a4 * x.val + a6))
        + 1)).sum
/-#check Nat.IsPrime 167-/


def compute_points_mod_p_sum_ (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  ∑ xy ∈  (Finset.univ.filter
    fun xy : (ZMod p) × (ZMod p) ↦
      letI x := xy.1
      letI y := xy.2
    y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6) , 1

/-
def compute_points_mod_p_sum (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  ∑ x ∈ (Finset.univ : Finset (ZMod p)),
  (∑ y ∈ (Finset.univ : Finset (ZMod p)) with
        (y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6) , (1 : ℤ))
-/

def compute_points_mod_p_sum (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  ∑ x ∈ (Finset.univ : Finset (ZMod p)),
  {y ∈ (Finset.univ : Finset (ZMod p))
  | y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x^2 + a4 * x + a6}.card

def compute_points_mod_p'_sum (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ :=
  ∑ x ∈ (Finset.univ : Finset (ZMod p)),
      (legendreSym p
        ((a1 * x.val + a3) ^ 2
        + 4 * (x.val ^ 3 + a2 * x.val ^ 2 + a4 * x.val + a6))
        + 1)

#eval compute_points_mod_p  157 (by decide) 1 0 0 (-784) (-8515)
#eval compute_points_mod_p' 157 (by decide) 1 0 0 (-784) (-8515)
#eval compute_points_mod_p_sum  157 (by decide) 1 0 0 (-784) (-8515)
#eval compute_points_mod_p'_sum 157 (by decide) 1 0 0 (-784) (-8515)


theorem compute_points_methods_equivalent (p : ℕ) (h : Fact p.Prime) (h2 : p ≠ 2) (a1 a2 a3 a4 a6 : ℤ) :
  compute_points_mod_p_sum p h a1 a2 a3 a4 a6 = compute_points_mod_p'_sum p h a1 a2 a3 a4 a6 := by
  rw [compute_points_mod_p_sum, compute_points_mod_p'_sum]
  -- Reduce to the per-x identity  #{y : Weierstrass eqn} = legendreSym p (discriminant) + 1.
  apply Finset.sum_congr rfl
  intro x _
  rw [← legendreSym.card_sqrts p h2
        ((a1 * ↑x.val + a3) ^ 2 + 4 * (↑x.val ^ 3 + a2 * ↑x.val ^ 2 + a4 * ↑x.val + a6)),
      Nat.cast_inj]
  -- `2 ≠ 0` and `4 ≠ 0` in `ZMod p` — the only place `p ≠ 2` is used.
  have hp : Nat.Prime p := Fact.out
  have two_ne : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun hd => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    intro hc; exact hnd ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast hc))
  have four_ne : (4 : ZMod p) ≠ 0 := by
    have h4 : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h4]; exact mul_ne_zero two_ne two_ne
  -- Completing the square is the bijection  y ↦ 2y + (a₁x + a₃)  between solutions of the
  -- Weierstrass equation in y and square roots of the discriminant (inverse z ↦ (z - c)/2).
  refine Finset.card_nbij'
      (fun y => 2 * y + (↑a1 * x + ↑a3))
      (fun z => (z - (↑a1 * x + ↑a3)) / 2) ?_ ?_ ?_ ?_
  · -- a solution y yields a square root 2y + c of the discriminant
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_toFinset, Set.mem_setOf_eq] at hy ⊢
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    linear_combination 4 * hy
  · -- a square root z yields back a solution (z - c)/2
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_toFinset, Set.mem_setOf_eq] at hz ⊢
    push_cast [ZMod.natCast_val, ZMod.cast_id] at hz
    set w := (z - (↑a1 * x + ↑a3)) / 2 with hw_def
    have hw : 2 * w = z - (↑a1 * x + ↑a3) := by rw [hw_def]; exact mul_div_cancel₀ _ two_ne
    have key : 4 * (w ^ 2 + ↑a1 * x * w + ↑a3 * w)
             = 4 * (x ^ 3 + ↑a2 * x ^ 2 + ↑a4 * x + ↑a6) := by
      linear_combination hz + (2 * w + (↑a1 * x + ↑a3) + z) * hw
    exact mul_left_cancel₀ four_ne key
  · -- the two maps are mutually inverse
    intro y _
    change (2 * y + (↑a1 * x + ↑a3) - (↑a1 * x + ↑a3)) / 2 = y
    field_simp; ring
  · intro z _
    change 2 * ((z - (↑a1 * x + ↑a3)) / 2) + (↑a1 * x + ↑a3) = z
    rw [mul_div_cancel₀ _ two_ne]; ring


noncomputable def L_factor_at_p_good (p : ℕ) (h : Fact p.Prime) (a1 a2 a3 a4 a6 : ℤ) : ℤ[X]:=
  letI points_mod_p := compute_points_mod_p p h a1 a2 a3 a4 a6
  1 - (p - (points_mod_p : ℤ)) • X + p • X^2

def p_is_good (p : ℕ) (h : Fact p.Prime)
    (a1 a2 a3 a4 a6 : ℤ) : Bool :=
  letI E : WeierstrassCurve ℤ :=
    { a₁ := a1
      a₂ := a2
      a₃ := a3
      a₄ := a4
      a₆ := a6 }
  decide (¬ ((p : ℤ) ∣ E.Δ))

def p_is_split_multiplicative (p : ℕ) (h : Fact p.Prime)
    (a1 a2 a3 a4 a6 : ℤ) : Bool :=
  letI E : WeierstrassCurve ℤ :=
    { a₁ := a1
      a₂ := a2
      a₃ := a3
      a₄ := a4
      a₆ := a6 }
  letI b2 := a1 ^ 2 + 4 * a2
  letI b4 := a1 * a3 + 2 * a4
  letI b6 := a3 ^ 2 + 4 * a6
  letI c4 := b2 ^ 2 - 24 * b4
  letI c6 := -b2 ^ 3 + 36 * b2 * b4 - 216 * b6
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ c4) ∧ (legendreSym p (-c6) = 1)

def p_is_non_split_multiplicative (p : ℕ) (h : Fact p.Prime)
    (a1 a2 a3 a4 a6 : ℤ) : Bool :=
  letI E : WeierstrassCurve ℤ :=
    { a₁ := a1
      a₂ := a2
      a₃ := a3
      a₄ := a4
      a₆ := a6 }
  letI b2 := a1 ^ 2 + 4 * a2
  letI b4 := a1 * a3 + 2 * a4
  letI b6 := a3 ^ 2 + 4 * a6
  letI c4 := b2 ^ 2 - 24 * b4
  letI c6 := -b2 ^ 3 + 36 * b2 * b4 - 216 * b6
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ c4) ∧ (legendreSym p (-c6) = -1)

-- Isogeny class: 21.a
-- Weierstrass curve: 21.a1
-- ⟨1, 0, 0, -784, -8515⟩
-- E : y^2 + xy = x^3 - 784x - 8515

-- p = 29 is a good prime for this curve

#eval p_is_good 29 (by decide) 1 0 0 (-784) (-8515)

theorem foo1 : L_factor_at_p_good 29 (by decide) 1 0 0 (-784) (-8515) = 1 + 2•X + 29•X^2 := by
  rw [L_factor_at_p_good, sub_eq_add_neg, ← neg_zsmul]
  rfl

theorem foo2 : p_is_good 29 (by decide) 1 0 0 (-784) (-8515) ∧
  L_factor_at_p_good 29 (by decide) 1 0 0 (-784) (-8515) = 1 + 2•X + 29•X^2 := by
  constructor
  · decide
  · exact foo1

-- p = 3 is a bad prime for this curve, split multiplicative reduction

#eval p_is_split_multiplicative 3 (by decide) 1 0 0 (-784) (-8515)

-- CONTINUE HERE...

-- p = 7 is a bad prime for this curve, non-split multiplicative reduction

#eval p_is_non_split_multiplicative 7 (by decide) 1 0 0 (-784) (-8515)

-- CONTINUE HERE...
