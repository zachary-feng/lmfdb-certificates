import Mathlib
open Polynomial

-- Set the elliptic curve E : y^2 + a₁xy + a₃y = x^3 + a₂x^2 + a₄x + a₆

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

#eval compute_points_mod_p_sum  157 (by decide) 1 0 0 (-784) (-8515)
#eval compute_points_mod_p'_sum 157 (by decide) 1 0 0 (-784) (-8515)


theorem compute_points_methods_equivalent (p : ℕ) (h : Fact p.Prime)
  (h2 : p ≠ 2) (a1 a2 a3 a4 a6 : ℤ) :
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

def E : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -784
  a₆ := -8515

-- Set the prime p

def p : ℕ := 29
local instance : Fact (Nat.Prime p) := by decide

-- The local L-factor on the LMFDB for this curve at the above prime is

noncomputable def L : ℤ[X] := 1 + 2 • X + 29 • X ^ 2

/-
  Affine point count over `ZMod p`.

  This computes the number of affine pairs `(x, y) ∈ 𝔽ₚ²` satisfying the
  Weierstrass equation for `E`.

  This does not include the point at infinity. Thus, for a nonsingular reduction,
  the full projective point count is usually this number plus `1`.
-/

def compute_points_mod_p [NeZero p] : ℤ :=
  (((Finset.univ : Finset ((ZMod p) × (ZMod p))).filter fun ⟨x, y⟩ =>
    y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x^2 + E.a₄ * x + E.a₆).card : ℤ)

/-
  Alternative affine point count using the Legendre symbol.

  Instead of enumerating all pairs `(x, y)`, this loops over `x ∈ 𝔽ₚ` and
  counts the number of corresponding `y` values by evaluating the quadratic
  discriminant in `y`.

  For the equation

    y² + (a₁x + a₃)y = x³ + a₂x² + a₄x + a₆,

  the relevant discriminant is

    (a₁x + a₃)² + 4(x³ + a₂x² + a₄x + a₆).

  The expression `legendreSym p D + 1` gives the number of solutions in `y`
  when `p` is an odd prime.
-/
def compute_points_mod_p' : ℤ :=
  ((Finset.univ : Finset (ZMod p)).val.map fun x : ZMod p =>
    legendreSym p
      ((E.a₁ * x.val + E.a₃) ^ 2 + 4 * (x.val ^ 3 +
        E.a₂ * x.val ^ 2 + E.a₄ * x.val + E.a₆)) + 1).sum

/-
  Local Euler factor at a good prime.

  For a good prime `p`, the local factor is written here as

    1 - a_p X + p X²,

  where

    a_p = p + 1 - #E(𝔽ₚ).

  Since `compute_points_mod_p` counts only affine points, the formula below uses

    p - compute_points_mod_p

  because the missing point at infinity contributes the extra `+1`.
-/
noncomputable def L_factor_at_p_good : ℤ[X] :=
  1 - (p - (compute_points_mod_p)) • X + p • X ^ 2

/-
  Reduction-type tests at the fixed prime `p`.

  These use the discriminant `E.Δ`, the invariant `E.c₄`, and the Legendre
  symbol of `-E.c₆` to classify the reduction behavior.

  The predicates below are Boolean-valued, so they can be evaluated with `#eval`.
-/

/--
Returns `true` when `p` is a good prime for the given Weierstrass model,
i.e. when `p` does not divide the discriminant.
-/
def p_is_good : Bool :=
  decide (¬ ((p : ℤ) ∣ E.Δ))

/--
Returns `true` when `p` is a split multiplicative prime.

This means that `p` divides the discriminant, `p` does not divide `c₄`,
and `-c₆` is a quadratic residue modulo `p`.
-/
def p_is_split_multiplicative : Bool :=
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ E.c₄) ∧ (legendreSym p (-E.c₆) = 1)

/--
Returns `true` when `p` is a nonsplit multiplicative prime.

This means that `p` divides the discriminant, `p` does not divide `c₄`,
and `-c₆` is a quadratic nonresidue modulo `p`.
-/
def p_is_non_split_multiplicative : Bool :=
  decide ((p : ℤ) ∣ E.Δ) ∧ (¬ (p : ℤ) ∣ E.c₄) ∧ (legendreSym p (-E.c₆) = -1)

/--
Returns `true` when `p` is an additive prime.

For this basic test, this is detected by checking whether `p` divides both
the discriminant and `c₄`.
-/
def p_is_additive : Bool :=
  decide ((p : ℤ) ∣ E.Δ) ∧ (p : ℤ) ∣ E.c₄

#eval p_is_good
#eval p_is_split_multiplicative
#eval p_is_non_split_multiplicative
#eval p_is_additive

theorem foo1 : p_is_good ∧ L_factor_at_p_good = L := by
  constructor
  · decide
  · rw [L_factor_at_p_good, sub_eq_add_neg, ← neg_zsmul]
    rfl
