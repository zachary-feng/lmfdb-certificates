import mathlib

def compute_sizes (p : ℕ) (h : Fact p.Prime) (a1 : ℤ) : ℤ :=
  ((Finset.univ : Finset (ZMod p)).val.map
    (fun x : (ZMod p) ↦ (1 : ℤ))).sum

def compute_sizes' (p : ℕ) (h : Fact p.Prime) (a1 : ℤ) : ℤ :=
  (Finset.univ.filter
    fun xy : (ZMod p) × (ZMod p) ↦
      letI x := xy.1
      letI y := xy.2
      x = (0 : ZMod p)
    ).card

def naive_sum (p : ℕ) (h : Fact p.Prime) : ℤ :=
  ∑ _ ∈ (Finset.univ : (Finset (ZMod p))), 1

#eval naive_sum 5 (by decide)

def naive_sum (p : ℕ)

#check legendreSym

#check compute_sizes 5 (by decide) 2
#eval compute_sizes 5 (by decide) 2

#eval compute_sizes' 5 (by decide) 2

def h := (Finset.univ : Finset (ZMod 3))
#check h

theorem same_method (p : ℕ) (h : Fact p.Prime) a1 :
  compute_sizes p h a1 = compute_sizes' p h a1 := by
  have h1 : compute_sizes p h a1 = ∑ x ∈ (Finset.univ : Finset (ZMod p)), (1:ℤ) := by
    rw [compute_sizes]
    rfl
  have h2 : compute_sizes' p h a1 = p := by
    sorry
  rw [h1, h2]
