import MeshfreeAddendum.Imports

/-!
# Weighted least-squares fits (abstract linear algebra)

This file contains the linear-algebra core behind Section 3 of the math addendum
("Moving least-squares operators"), stated for an arbitrary finite family of data
points `J` and an arbitrary finite basis indexed by `ι`.

* `gram w φ` is the moment matrix `Ñ = ∑ⱼ wⱼ φⱼ φⱼᵀ`.
* `lsWeight w φ e j = wⱼ eₑᵀ Ñ⁻¹ φⱼ` are the weights of eq. (3.2) `eq:cij` of the addendum.
* `lsCoeff w φ f = Ñ⁻¹ ∑ⱼ wⱼ φⱼ fⱼ` is the least-squares coefficient vector.

Main results:
* `gram_isUnit`              : unisolvency + positive weights ⇒ `Ñ` invertible.
* `lsCoeff_minimizes`        : `lsCoeff` minimises the weighted squared residual.
* `lsWeight_reproduces`      : reproduction, the core of Lemma 3.3(i).
* `lsWeight_sum_eq_zero`     : zero row sums, Lemma 3.3(ii).
* `lsWeight_scale`           : diagonal rescaling of the basis, Lemma 3.3(iii) and
                               the scaling step in the proof of Lemma 3.5.
* `lsWeight_reflect`         : antisymmetry on centrally symmetric stencils, Lemma 3.7(i).
* `sum_odd_mul_even`         : the cancellation used in Lemma 3.7(ii) and Prop. 4.4.
-/

open Matrix Finset

namespace Meshfree

set_option linter.unusedSectionVars false

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]

/-- The moment (Gram) matrix `Ñ = ∑ⱼ wⱼ φⱼ φⱼᵀ`. -/
def gram (w : J → ℝ) (φ : J → ι → ℝ) : Matrix ι ι ℝ :=
  fun a b => ∑ j, w j * φ j a * φ j b

/-- The least-squares weight of data point `j` for the coefficient `e`:
`wⱼ eₑᵀ Ñ⁻¹ φⱼ` (eq. (3.2) `eq:cij` of the addendum). -/
noncomputable def lsWeight (w : J → ℝ) (φ : J → ι → ℝ) (e : ι) (j : J) : ℝ :=
  w j * ((gram w φ)⁻¹ *ᵥ φ j) e

/-- The right-hand side `b = ∑ⱼ wⱼ φⱼ fⱼ` of the normal equations. -/
def rhs (w : J → ℝ) (φ : J → ι → ℝ) (f : J → ℝ) : ι → ℝ :=
  fun a => ∑ j, w j * φ j a * f j

/-- The least-squares coefficient vector `Ñ⁻¹ b`. -/
noncomputable def lsCoeff (w : J → ℝ) (φ : J → ι → ℝ) (f : J → ℝ) : ι → ℝ :=
  (gram w φ)⁻¹ *ᵥ rhs w φ f

/-- Unisolvency (Definition 3.1, abstract form): the only coefficient vector whose
basis expansion vanishes at all data points is zero. -/
def Unisolvent (φ : J → ι → ℝ) : Prop :=
  ∀ a : ι → ℝ, (∀ j, φ j ⬝ᵥ a = 0) → a = 0

/-- The weighted squared residual of a coefficient vector `a` for data `f`. -/
def residual (w : J → ℝ) (φ : J → ι → ℝ) (f : J → ℝ) (a : ι → ℝ) : ℝ :=
  ∑ j, w j * (φ j ⬝ᵥ a - f j) ^ 2

variable (w : J → ℝ) (φ : J → ι → ℝ)

theorem gram_mulVec (a : ι → ℝ) :
    gram w φ *ᵥ a = fun b => ∑ j, w j * (φ j ⬝ᵥ a) * φ j b := by
  funext b
  simp only [mulVec, dotProduct, gram, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem rhs_eq_gram_mulVec (a : ι → ℝ) :
    rhs w φ (fun j => φ j ⬝ᵥ a) = gram w φ *ᵥ a := by
  rw [gram_mulVec]
  funext b
  simp only [rhs]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dotProduct_gram_mulVec (a : ι → ℝ) :
    a ⬝ᵥ (gram w φ *ᵥ a) = ∑ j, w j * (φ j ⬝ᵥ a) ^ 2 := by
  rw [gram_mulVec]
  calc a ⬝ᵥ (fun b => ∑ j, w j * (φ j ⬝ᵥ a) * φ j b)
      = ∑ b, ∑ j, a b * (w j * (φ j ⬝ᵥ a) * φ j b) := by
        simp only [dotProduct, Finset.mul_sum]
    _ = ∑ j, ∑ b, a b * (w j * (φ j ⬝ᵥ a) * φ j b) := Finset.sum_comm
    _ = ∑ j, w j * (φ j ⬝ᵥ a) * (φ j ⬝ᵥ a) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∀ b, a b * (w j * (φ j ⬝ᵥ a) * φ j b) = (w j * (φ j ⬝ᵥ a)) * (φ j b * a b) :=
          fun b => by ring
        simp only [this, ← Finset.mul_sum]
        rfl
    _ = ∑ j, w j * (φ j ⬝ᵥ a) ^ 2 := by
        exact Finset.sum_congr rfl fun j _ => by ring

/-- With positive weights and a unisolvent basis the moment matrix is invertible
(the addendum states the stronger fact that it is positive definite; invertibility
is all that the proofs use). -/
theorem gram_isUnit (hw : ∀ j, 0 < w j) (hU : Unisolvent φ) : IsUnit (gram w φ).det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  have key : ∀ a, gram w φ *ᵥ a = 0 → a = 0 := by
    intro a ha
    apply hU
    have h0 : ∑ j, w j * (φ j ⬝ᵥ a) ^ 2 = 0 := by
      rw [← dotProduct_gram_mulVec, ha, dotProduct_zero]
    have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ w j * (φ j ⬝ᵥ a) ^ 2 :=
      fun j _ => mul_nonneg (hw j).le (sq_nonneg _)
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (mem_univ j)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hw j).ne'
    · simpa using h
  intro a b hab
  have : gram w φ *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  exact sub_eq_zero.1 (key _ this)

variable {w φ}

/-- The least-squares coefficients are the coefficients of the weights:
`(lsCoeff f)ₑ = ∑ⱼ lsWeight e j * fⱼ`. -/
theorem lsCoeff_apply (f : J → ℝ) (e : ι) :
    lsCoeff w φ f e = ∑ j, lsWeight w φ e j * f j := by
  simp only [lsCoeff, lsWeight, mulVec, dotProduct, rhs, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- Reproduction (core of Lemma 3.3(i)): if the data are exactly a basis expansion
with coefficients `a`, the least-squares coefficients are `a`. -/
theorem lsCoeff_reproduces (hN : IsUnit (gram w φ).det) (a : ι → ℝ) :
    lsCoeff w φ (fun j => φ j ⬝ᵥ a) = a := by
  rw [lsCoeff, rhs_eq_gram_mulVec, mulVec_mulVec, nonsing_inv_mul _ hN, one_mulVec]

/-- Lemma 3.3(i), abstract form: `∑ⱼ cⱼ g(xⱼ) = aₑ` whenever `g = ∑ aₐ φₐ`. -/
theorem lsWeight_reproduces (hN : IsUnit (gram w φ).det) (a : ι → ℝ) (e : ι) :
    ∑ j, lsWeight w φ e j * (φ j ⬝ᵥ a) = a e := by
  rw [← lsCoeff_apply, lsCoeff_reproduces hN]

/-- Lemma 3.3(ii), abstract form: if the basis contains the constant function
`e₀` and `e ≠ e₀`, the weights have zero sum. -/
theorem lsWeight_sum_eq_zero (hN : IsUnit (gram w φ).det) {e₀ e : ι}
    (hconst : ∀ j, φ j e₀ = 1) (he : e ≠ e₀) : ∑ j, lsWeight w φ e j = 0 := by
  have h := lsWeight_reproduces hN (Pi.single e₀ 1) e
  have hφ : ∀ j, φ j ⬝ᵥ Pi.single e₀ 1 = 1 := fun j => by
    rw [dotProduct_single, hconst, mul_one]
  simp only [hφ, mul_one] at h
  rw [h, Pi.single_eq_of_ne he]

/-- The least-squares coefficient vector minimises the weighted residual
(so that `lsWeight` are indeed the least-squares weights). -/
theorem lsCoeff_minimizes (hw : ∀ j, 0 ≤ w j) (hN : IsUnit (gram w φ).det)
    (f : J → ℝ) (a : ι → ℝ) :
    residual w φ f (lsCoeff w φ f) ≤ residual w φ f a := by
  set a₀ := lsCoeff w φ f
  set δ := a - a₀
  have hnormal : gram w φ *ᵥ a₀ = rhs w φ f := by
    simp only [a₀, lsCoeff, mulVec_mulVec, mul_nonsing_inv _ hN, one_mulVec]
  -- cross term vanishes by the normal equations
  have hcross : ∑ j, w j * (φ j ⬝ᵥ a₀ - f j) * (φ j ⬝ᵥ δ) = 0 := by
    have h1 : ∑ j, w j * (φ j ⬝ᵥ a₀) * (φ j ⬝ᵥ δ) = δ ⬝ᵥ (gram w φ *ᵥ a₀) := by
      rw [gram_mulVec]
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    have h2 : ∑ j, w j * f j * (φ j ⬝ᵥ δ) = δ ⬝ᵥ rhs w φ f := by
      simp only [dotProduct, rhs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    have : ∑ j, w j * (φ j ⬝ᵥ a₀ - f j) * (φ j ⬝ᵥ δ)
        = ∑ j, w j * (φ j ⬝ᵥ a₀) * (φ j ⬝ᵥ δ) - ∑ j, w j * f j * (φ j ⬝ᵥ δ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, h1, h2, hnormal, sub_self]
  have ha : a = a₀ + δ := by simp [δ]
  have hexp : residual w φ f a = residual w φ f a₀ + ∑ j, w j * (φ j ⬝ᵥ δ) ^ 2 := by
    simp only [residual]
    rw [ha]
    have : ∀ j, w j * (φ j ⬝ᵥ (a₀ + δ) - f j) ^ 2
        = w j * (φ j ⬝ᵥ a₀ - f j) ^ 2 + 2 * (w j * (φ j ⬝ᵥ a₀ - f j) * (φ j ⬝ᵥ δ))
          + w j * (φ j ⬝ᵥ δ) ^ 2 := by
      intro j; rw [dotProduct_add]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]
  rw [hexp]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _))

/-- Lemma 3.3(iii) / proof of Lemma 3.5, abstract form: rescaling every basis
function by a non-zero factor `sₐ` divides the weights of coefficient `e` by `sₑ`. -/
theorem lsWeight_scale (s : ι → ℝ) (hs : ∀ a, s a ≠ 0) (e : ι) (j : J) :
    lsWeight w (fun j a => s a * φ j a) e j = (s e)⁻¹ * lsWeight w φ e j := by
  set S : Matrix ι ι ℝ := diagonal s
  set Si : Matrix ι ι ℝ := diagonal (fun a => (s a)⁻¹)
  have hgram : gram w (fun j a => s a * φ j a) = S * gram w φ * S := by
    ext a b
    simp only [gram, S, mul_diagonal, diagonal_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hSiS : Si * S = 1 := by
    simp only [Si, S, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1; funext a; exact inv_mul_cancel₀ (hs a)
  have hinv : (gram w (fun j a => s a * φ j a))⁻¹ = Si * (gram w φ)⁻¹ * Si := by
    rw [hgram, Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_eq_left_inv hSiS, Matrix.mul_assoc]
  simp only [lsWeight, hinv]
  have hφ : (fun a => s a * φ j a) = S *ᵥ φ j := by
    funext a; simp [S, mulVec_diagonal]
  rw [hφ, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hSiS, Matrix.mul_one,
    ← mulVec_mulVec]
  simp only [Si, mulVec_diagonal]
  ring

/-- Lemma 3.7(i), abstract form. Let `ρ` be a permutation of the data points
(the involution `j ↦ j'`) and `P` a diagonal of signs such that `φ (ρ j) = P φ j`
and `w (ρ j) = w j`. If `P e = -1` then `c_{e, ρ j} = - c_{e, j}`. -/
theorem lsWeight_reflect (ρ : Equiv.Perm J) (P : ι → ℝ) (hP : ∀ a, P a = 1 ∨ P a = -1)
    (hφ : ∀ j a, φ (ρ j) a = P a * φ j a) (hwρ : ∀ j, w (ρ j) = w j)
    {e : ι} (he : P e = -1) (j : J) :
    lsWeight w φ e (ρ j) = - lsWeight w φ e j := by
  have hPne : ∀ a, P a ≠ 0 := fun a => by rcases hP a with h | h <;> rw [h] <;> norm_num
  have hgram : gram w (fun j a => P a * φ j a) = gram w φ := by
    ext a b
    simp only [gram]
    rw [← Equiv.sum_comp ρ (fun k => w k * φ k a * φ k b)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hwρ, hφ, hφ]
  have h1 := lsWeight_scale (w := w) (φ := φ) P hPne e j
  have h2 : lsWeight w (fun j a => P a * φ j a) e j = lsWeight w φ e (ρ j) := by
    simp only [lsWeight, hgram, hwρ]
    congr 2
    funext a; rw [hφ]
  rw [← h2, h1, he]
  norm_num

/-- Cancellation of an odd weight against even data: if `c (ρ j) = -c j` and
`g (ρ j) = g j` then `∑ⱼ cⱼ gⱼ = 0`. Used in Lemma 3.7(ii) and Proposition 4.4. -/
theorem sum_odd_mul_even (ρ : Equiv.Perm J) (c g : J → ℝ) (hc : ∀ j, c (ρ j) = - c j)
    (hg : ∀ j, c j ≠ 0 → g (ρ j) = g j) : ∑ j, c j * g j = 0 := by
  have h : ∑ j, c j * g j = ∑ j, c (ρ j) * g (ρ j) := (Equiv.sum_comp ρ _).symm
  have h' : ∑ j, c (ρ j) * g (ρ j) = - ∑ j, c j * g j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : c j = 0
    · simp [hc, hj]
    · rw [hc, hg j hj]; ring
  linarith

/-- Reindexing the basis by an equivalence does not change the weights. -/
theorem lsWeight_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (a : ι')
    (j : J) : lsWeight w (fun j b => φ j (e b)) a j = lsWeight w φ (e a) j := by
  have hg : gram w (fun j b => φ j (e b)) = (gram w φ).submatrix e e := by
    ext; simp [gram]
  simp only [lsWeight, hg, inv_submatrix_equiv, submatrix_mulVec_equiv]
  simp [Function.comp_def]

end Meshfree
