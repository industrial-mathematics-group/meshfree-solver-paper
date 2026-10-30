import MeshfreeAddendum.LeastSquares

/-!
# Taylor bases, polynomial spaces and partial derivatives (Sections 2.3 and 3)

* `mis D q`      : multi-indices `α ∈ ℕ^D` with `|α| ≤ q`.
* `mono α y`     : the Taylor monomial `y^α / α!`.
* `Poly D q`     : functions `ℝ^D → ℝ` that are polynomials of degree `≤ q`, i.e.
                   finite combinations of Taylor monomials of degree `≤ q`
                   (this is the space `Π_q` of the addendum).
* `pd g z d`     : the partial derivative `∂_d g(z)`, defined analytically as the
                   derivative of `t ↦ g(z + t e_d)` at `t = 0`.

The main result here is `pd_poly`: the partial derivative at `0` of a polynomial
is its Taylor coefficient of the multi-index `e_d`. This is the step
"its coefficient of `y_d` is `∂_d g(0)`" in the proof of Lemma 3.3(i).
-/

open Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Meshfree

variable {D : ℕ}

/-- Points of `ℝ^D`. -/
abbrev Pt (D : ℕ) := Fin D → ℝ

/-- Total degree `|α|` of a multi-index. -/
def deg (α : Fin D → ℕ) : ℕ := ∑ i, α i

/-- Multi-indices of total degree at most `q`. -/
def mis (D q : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ => range (q + 1)).filter (fun α => deg α ≤ q)

theorem le_deg (α : Fin D → ℕ) (i : Fin D) : α i ≤ deg α :=
  Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (mem_univ i)

@[simp] theorem mem_mis {q : ℕ} {α : Fin D → ℕ} : α ∈ mis D q ↔ deg α ≤ q := by
  simp only [mis, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i
  exact Nat.lt_succ_of_le ((le_deg α i).trans h)

theorem mis_mono {r q : ℕ} (h : r ≤ q) : mis D r ⊆ mis D q := fun α hα => by
  rw [mem_mis] at *; omega

/-- The unit multi-index `e_d`. -/
def unit (d : Fin D) : Fin D → ℕ := Pi.single d 1

theorem deg_unit (d : Fin D) : deg (unit d) = 1 := by
  simp [deg, unit]

theorem deg_zero : deg (0 : Fin D → ℕ) = 0 := by simp [deg]

theorem unit_mem_mis {q : ℕ} (hq : 1 ≤ q) (d : Fin D) : unit d ∈ mis D q := by
  rw [mem_mis, deg_unit]; exact hq

theorem zero_mem_mis (q : ℕ) : (0 : Fin D → ℕ) ∈ mis D q := by
  rw [mem_mis, deg_zero]; exact Nat.zero_le _

theorem unit_ne_zero (d : Fin D) : unit d ≠ 0 := by
  intro h
  have := congrFun h d
  simp [unit] at this

/-- The Taylor monomial `y^α / α!`. -/
noncomputable def mono (α : Fin D → ℕ) (y : Pt D) : ℝ :=
  ∏ i, y i ^ α i / ((α i).factorial : ℝ)

@[simp] theorem mono_zero (y : Pt D) : mono 0 y = 1 := by
  simp [mono]

theorem mono_unit (d : Fin D) (y : Pt D) : mono (unit d) y = y d := by
  simp only [mono, unit]
  rw [← Finset.mul_prod_erase univ _ (mem_univ d)]
  rw [Finset.prod_eq_one]
  · simp
  · intro i hi
    have : i ≠ d := ne_of_mem_erase hi
    simp [Pi.single_apply, this]

/-- Homogeneity: `(θ y)^α/α! = θ^{|α|} y^α/α!`. -/
theorem mono_smul (α : Fin D → ℕ) (θ : ℝ) (y : Pt D) :
    mono α (θ • y) = θ ^ deg α * mono α y := by
  simp only [mono, deg, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem mono_neg (α : Fin D → ℕ) (y : Pt D) :
    mono α (-y) = (-1) ^ deg α * mono α y := by
  rw [← mono_smul]; congr 1; funext i; simp

/-- The polynomial space `Π_q`: polynomials of degree at most `q`, written in the
Taylor basis. -/
def Poly (D q : ℕ) : Set (Pt D → ℝ) :=
  {g | ∃ a : (Fin D → ℕ) → ℝ, ∀ y, g y = ∑ α ∈ mis D q, a α * mono α y}

theorem Poly.mono {r q : ℕ} (h : r ≤ q) {g : Pt D → ℝ} (hg : g ∈ Poly D r) :
    g ∈ Poly D q := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun α => if α ∈ mis D r then a α else 0, fun y => ?_⟩
  rw [ha, ← Finset.sum_subset (mis_mono h)]
  · exact Finset.sum_congr rfl fun α hα => by simp [hα]
  · intro α _ hα; simp [hα]

/-- The partial derivative `∂_d g(z)`. -/
noncomputable def pd (g : Pt D → ℝ) (z : Pt D) (d : Fin D) : ℝ :=
  deriv (fun t : ℝ => g (z + Pi.single d t)) 0

theorem pd_shift (g : Pt D → ℝ) (z : Pt D) (d : Fin D) :
    pd g z d = pd (fun y => g (z + y)) 0 d := by
  simp [pd]

theorem mono_single (α : Fin D → ℕ) (d : Fin D) (t : ℝ) :
    mono α (Pi.single d t) =
      if (∀ i, i ≠ d → α i = 0) then t ^ α d / ((α d).factorial : ℝ) else 0 := by
  unfold mono
  rw [← Finset.mul_prod_erase univ _ (mem_univ d)]
  have h : ∀ i ∈ univ.erase d,
      (Pi.single d t : Pt D) i ^ α i / ((α i).factorial : ℝ) = if α i = 0 then 1 else 0 := by
    intro i hi
    have hid : i ≠ d := ne_of_mem_erase hi
    by_cases h0 : α i = 0
    · simp [h0]
    · simp [Pi.single_apply, hid, h0, zero_pow h0]
  rw [Finset.prod_congr rfl h, Finset.prod_boole]
  simp only [Pi.single_eq_same, mem_erase, ne_eq, mem_univ, and_true]
  split_ifs <;> simp

theorem hasDerivAt_pow_div_factorial (n : ℕ) :
    HasDerivAt (fun t : ℝ => t ^ n / (n.factorial : ℝ)) (if n = 1 then 1 else 0) 0 := by
  have h := (hasDerivAt_pow n (0 : ℝ)).div_const (n.factorial : ℝ)
  convert h using 1
  rcases n with _ | _ | n
  · simp
  · simp
  · simp

/-- The partial derivative at `0` of a polynomial is its `e_d` Taylor coefficient. -/
theorem pd_poly {q : ℕ} (hq : 1 ≤ q) (a : (Fin D → ℕ) → ℝ) (g : Pt D → ℝ)
    (hg : ∀ y, g y = ∑ α ∈ mis D q, a α * mono α y) (d : Fin D) :
    pd g 0 d = a (unit d) := by
  have hfun : (fun t : ℝ => g (0 + Pi.single d t)) =
      fun t => ∑ α ∈ mis D q, a α *
        (if (∀ i, i ≠ d → α i = 0) then t ^ α d / ((α d).factorial : ℝ) else 0) := by
    funext t
    rw [zero_add, hg]
    exact Finset.sum_congr rfl fun α _ => by rw [mono_single]
  have hderiv : HasDerivAt (fun t : ℝ => g (0 + Pi.single d t))
      (∑ α ∈ mis D q, a α *
        (if (∀ i, i ≠ d → α i = 0) then (if α d = 1 then 1 else 0) else 0)) 0 := by
    rw [hfun]
    apply HasDerivAt.fun_sum
    intro α _
    apply HasDerivAt.const_mul
    by_cases h : ∀ i, i ≠ d → α i = 0
    · rw [if_pos h]
      exact (hasDerivAt_pow_div_factorial (α d)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => if_pos h)
    · rw [if_neg h]
      exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => if_neg h)
  rw [pd, hderiv.deriv]
  rw [Finset.sum_eq_single (unit d)]
  · have h1 : ∀ i, i ≠ d → unit d i = 0 := fun i hi => by simp [unit, Pi.single_apply, hi]
    rw [if_pos h1]
    simp [unit]
  · intro α _ hα
    split_ifs with h1 h2
    · exfalso; apply hα
      funext i
      by_cases hi : i = d
      · subst hi; simp [unit, h2]
      · simp [unit, Pi.single_apply, hi, h1 i hi]
    · simp
    · simp
  · intro h; exact absurd (unit_mem_mis hq d) h

theorem pd_poly' {q : ℕ} (hq : 1 ≤ q) {g : Pt D → ℝ} (a : (Fin D → ℕ) → ℝ)
    (hg : ∀ y, g y = ∑ α ∈ mis D q, a α * mono α y) (d : Fin D) :
    pd g 0 d = a (unit d) := pd_poly hq a g hg d

end Meshfree
