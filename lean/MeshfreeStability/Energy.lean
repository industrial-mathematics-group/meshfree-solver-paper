import MeshfreeStability.Imports

/-!
# The energy method

Generic tools used throughout the stability note.

* Linear semi-discrete schemes are matrices `L : Matrix ι ι ℝ` on a finite particle set `ι`.
  Stability is stated for **every solution** `U : ℝ → ι → ℝ` of `U' = L U` (a semigroup bound
  `‖e^{tL}‖ ≤ C e^{ωt}` is the same statement, since `t ↦ e^{tL}U₀` is the solution).
* `qf W u = uᵀ W u` is the energy of a symmetric weight matrix `W`; diagonal weights
  `W = diag H` give the weighted norms `‖u‖²_H = ∑ H_i u_i²` of the note.
* `energy_bound`: if `uᵀ W L u ≤ ω uᵀ W u` for all `u`, then `qf W (U t) ≤ e^{2ωt} qf W (U 0)`.
* `energy_forced`: dissipative system with a bounded forcing, `‖x(t)‖ ≤ ‖x(0)‖ + M t`.
* `banded_qf_le`: a matrix with `≤ b` nonzero entries per row and column, all bounded by `ε`,
  has `|uᵀ R u| ≤ b ε |u|²`.
-/

open Finset Matrix

namespace Meshfree.Stability

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `uᵀ W u`. -/
def qf (W : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := u ⬝ᵥ (W *ᵥ u)

/-- The weighted inner product `∑ H_i u_i v_i`. -/
def wip (H u v : ι → ℝ) : ℝ := ∑ i, H i * u i * v i

/-- Euclidean squared norm `|u|² = ∑ u_i²`. -/
def esq (u : ι → ℝ) : ℝ := ∑ i, u i ^ 2

theorem qf_eq_sum (W : Matrix ι ι ℝ) (u : ι → ℝ) :
    qf W u = ∑ i, ∑ j, u i * W i j * u j := by
  simp only [qf, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qf_diagonal [DecidableEq ι] (H u : ι → ℝ) : qf (diagonal H) u = wip H u u := by
  simp only [qf, wip, dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem wip_self_nonneg {H : ι → ℝ} (hH : ∀ i, 0 ≤ H i) (u : ι → ℝ) : 0 ≤ wip H u u :=
  Finset.sum_nonneg fun i _ => by rw [mul_assoc]; exact mul_nonneg (hH i) (mul_self_nonneg _)

theorem esq_nonneg (u : ι → ℝ) : 0 ≤ esq u := Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Weighted Cauchy–Schwarz inequality. -/
theorem wip_le_sqrt_mul_sqrt {H : ι → ℝ} (hH : ∀ i, 0 ≤ H i) (u v : ι → ℝ) :
    wip H u v ≤ Real.sqrt (wip H u u) * Real.sqrt (wip H v v) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => Real.sqrt (H i) * u i)
    (fun i => Real.sqrt (H i) * v i)
  have e1 : ∀ w z : ι → ℝ, ∑ i, Real.sqrt (H i) * w i * (Real.sqrt (H i) * z i) = wip H w z := by
    intro w z; refine Finset.sum_congr rfl fun i _ => ?_
    have := Real.mul_self_sqrt (hH i)
    calc Real.sqrt (H i) * w i * (Real.sqrt (H i) * z i)
        = (Real.sqrt (H i) * Real.sqrt (H i)) * w i * z i := by ring
      _ = _ := by rw [this]
  have e2 : ∀ w : ι → ℝ, ∑ i, (Real.sqrt (H i) * w i) ^ 2 = wip H w w := by
    intro w; rw [← e1 w w]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e2] at hcs
  rw [← Real.sqrt_mul (wip_self_nonneg hH u)]
  exact Real.le_sqrt_of_sq_le hcs

/-- Derivative of the energy `uᵀWu` along a differentiable curve, `W` symmetric. -/
theorem hasDerivAt_qf {W : Matrix ι ι ℝ} (hW : Wᵀ = W) {U : ℝ → ι → ℝ} {U' : ι → ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) :
    HasDerivAt (fun s => qf W (U s)) (2 * (U t ⬝ᵥ (W *ᵥ U'))) t := by
  have hUi : ∀ i, HasDerivAt (fun s => U s i) (U' i) t := fun i => (hasDerivAt_pi.1 hU) i
  have h : HasDerivAt (fun s => ∑ i, ∑ j, U s i * W i j * U s j)
      (∑ i, ∑ j, (U' i * W i j * U t j + U t i * W i j * U' j)) t := by
    apply HasDerivAt.fun_sum; intro i _
    apply HasDerivAt.fun_sum; intro j _
    exact ((hUi i).mul_const (W i j)).mul (hUi j)
  simp only [qf_eq_sum]
  convert h using 1
  have hsym : ∑ i, ∑ j, U' i * W i j * U t j = ∑ i, ∑ j, U t i * W i j * U' j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : W j i = W i j := by rw [← transpose_apply W i j, hW]
    rw [this]; ring
  have e : U t ⬝ᵥ (W *ᵥ U') = ∑ i, ∑ j, U t i * W i j * U' j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  simp only [Finset.sum_add_distrib]
  rw [hsym, e]; ring

/-- **The energy method.** If `uᵀ W L u ≤ ω uᵀ W u` for all `u` (the numerical abscissa of `L`
in the `W`-energy is at most `ω`), then every solution of `U' = LU` satisfies
`uᵀWu(t) ≤ e^{2ωt} uᵀWu(0)` for `t ≥ 0`. -/
theorem energy_bound {W L : Matrix ι ι ℝ} (hW : Wᵀ = W) {ω : ℝ}
    (hω : ∀ u, u ⬝ᵥ (W *ᵥ (L *ᵥ u)) ≤ ω * qf W u)
    {U : ℝ → ι → ℝ} (hU : ∀ t, HasDerivAt U (L *ᵥ U t) t) {t : ℝ} (ht : 0 ≤ t) :
    qf W (U t) ≤ Real.exp (2 * ω * t) * qf W (U 0) := by
  set f : ℝ → ℝ := fun s => Real.exp (-(2 * ω * s)) * qf W (U s)
  have hf : ∀ s, HasDerivAt f (Real.exp (-(2 * ω * s)) * (-(2 * ω)) * qf W (U s)
      + Real.exp (-(2 * ω * s)) * (2 * (U s ⬝ᵥ (W *ᵥ (L *ᵥ U s))))) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-(2 * ω * s))) (Real.exp (-(2 * ω * s)) * (-(2 * ω))) s := by
      have := ((hasDerivAt_id s).const_mul (2 * ω)).neg.exp
      simpa using this
    exact h1.mul (hasDerivAt_qf hW (hU s))
  have hanti : Antitone f := by
    refine antitone_of_hasDerivAt_nonpos hf fun s => ?_
    have h2 := mul_le_mul_of_nonneg_left (hω (U s))
      (by positivity : (0:ℝ) ≤ 2 * Real.exp (-(2 * ω * s)))
    show _ ≤ (0 : ℝ)
    nlinarith [h2]
  have := hanti ht
  simp only [f, mul_zero, neg_zero, Real.exp_zero, one_mul] at this
  have he := Real.exp_pos (2 * ω * t)
  calc qf W (U t) = Real.exp (2 * ω * t) * (Real.exp (-(2 * ω * t)) * qf W (U t)) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (2 * ω * t) * qf W (U 0) := mul_le_mul_of_nonneg_left this he.le

/-- Norm form of `energy_bound` (taking square roots). -/
theorem energy_bound_sqrt {W L : Matrix ι ι ℝ} (hW : Wᵀ = W) {ω : ℝ}
    (hω : ∀ u, u ⬝ᵥ (W *ᵥ (L *ᵥ u)) ≤ ω * qf W u)
    {U : ℝ → ι → ℝ} (hU : ∀ t, HasDerivAt U (L *ᵥ U t) t) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (qf W (U t)) ≤ Real.exp (ω * t) * Real.sqrt (qf W (U 0)) := by
  have h := energy_bound hW hω hU ht
  have : Real.exp (2 * ω * t) = Real.exp (ω * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]; ring_nf
  rw [this] at h
  calc Real.sqrt (qf W (U t)) ≤ Real.sqrt (Real.exp (ω * t) ^ 2 * qf W (U 0)) :=
        Real.sqrt_le_sqrt h
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

/-- **Energy estimate with a forcing term** (diagonal weight, dissipative operator).
If `∑ H_i u_i (Au)_i ≤ 0` for all `u` and `x' = A x + f(t)` with `‖f(t)‖_H ≤ M`, then
`‖x(t)‖_H ≤ ‖x(0)‖_H + M t` for `t ≥ 0`. This is Duhamel's formula combined with
contractivity, written without the semigroup. -/
theorem energy_forced {H : ι → ℝ} (hH : ∀ i, 0 ≤ H i) {A : Matrix ι ι ℝ}
    (hA : ∀ u, wip H u (A *ᵥ u) ≤ 0) {x f : ℝ → ι → ℝ} {M : ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + f t) t)
    (hf : ∀ t, 0 ≤ t → Real.sqrt (wip H (f t) (f t)) ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (wip H (x t) (x t)) ≤ Real.sqrt (wip H (x 0) (x 0)) + M * t := by
  classical
  have hW : (diagonal H)ᵀ = diagonal H := diagonal_transpose H
  -- `E s = ‖x s‖²_H`
  set E : ℝ → ℝ := fun s => wip H (x s) (x s)
  have hE : ∀ s, HasDerivAt E (2 * wip H (x s) (A *ᵥ x s + f s)) s := by
    intro s
    have := hasDerivAt_qf hW (hx s)
    simp only [qf_diagonal] at this
    convert this using 1
    simp only [wip, dotProduct, mulVec_diagonal]
    congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  have hE0 : ∀ s, 0 ≤ E s := fun s => wip_self_nonneg hH _
  -- for every δ > 0, `√(E + δ²) - M s` is antitone on `[0, ∞)`
  have key : ∀ δ > 0, Real.sqrt (E t + δ ^ 2) ≤ Real.sqrt (E 0 + δ ^ 2) + M * t := by
    intro δ hδ
    set g : ℝ → ℝ := fun s => Real.sqrt (E s + δ ^ 2) - M * s
    have hpos : ∀ s, 0 < E s + δ ^ 2 := fun s => by have := hE0 s; positivity
    have hg : ∀ s, HasDerivAt g (2 * wip H (x s) (A *ᵥ x s + f s) /
        (2 * Real.sqrt (E s + δ ^ 2)) - M) s := by
      intro s
      have h1 := ((hE s).add_const (δ ^ 2)).sqrt (hpos s).ne'
      have h2 : HasDerivAt (fun y => M * y) M s := by
        simpa using (hasDerivAt_id s).const_mul M
      exact h1.sub h2
    have hanti : AntitoneOn g (Set.Ici 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
      · exact (fun s _ => (hg s).continuousAt.continuousWithinAt)
      · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        have hs0 : 0 ≤ s := le_of_lt hs
        rw [(hg s).deriv]
        have hsq := Real.sqrt_pos.2 (hpos s)
        have hsplit : wip H (x s) (A *ᵥ x s + f s) = wip H (x s) (A *ᵥ x s) + wip H (x s) (f s) := by
          simp only [wip, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        have hcs := wip_le_sqrt_mul_sqrt hH (x s) (f s)
        have hEs : Real.sqrt (E s) ≤ Real.sqrt (E s + δ ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
        have hfs := hf s hs0
        have hM : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hfs
        have : wip H (x s) (f s) ≤ Real.sqrt (E s + δ ^ 2) * M :=
          hcs.trans (mul_le_mul hEs hfs (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        rw [div_sub' (by positivity), div_nonpos_iff]
        right
        refine ⟨?_, by positivity⟩
        have := hA (x s)
        nlinarith
    have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    simp only [g, mul_zero, sub_zero] at this
    linarith
  -- let `δ → 0`
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h := key (ε / 2) (half_pos hε)
  have h1 : Real.sqrt (E t) ≤ Real.sqrt (E t + (ε / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt (E 0 + (ε / 2) ^ 2) ≤ Real.sqrt (E 0) + ε / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt (hE0 0)
    nlinarith [Real.sqrt_nonneg (E 0)]
  show Real.sqrt (E t) < Real.sqrt (E 0) + M * t + ε
  linarith

/-- **Existence of solutions of linear systems** (`U(t) = e^{tL} v`), via the matrix exponential
with the `ℓ^∞` operator norm. -/
theorem linear_ode_exists [DecidableEq ι] (L : Matrix ι ι ℝ) (v : ι → ℝ) :
    ∃ U : ℝ → ι → ℝ, U 0 = v ∧ ∀ t, HasDerivAt U (L *ᵥ U t) t := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  let φl : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => add_mulVec M N v
      map_smul' := fun r M => by simp [smul_mulVec] }
  let φ : Matrix ι ι ℝ →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap φl
  refine ⟨fun t => NormedSpace.exp (t • L) *ᵥ v, by simp, fun t => ?_⟩
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t
  have h2 := φ.hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun t => NormedSpace.exp (t • L) *ᵥ v)
      (φ (L * NormedSpace.exp (t • L))) t := h2
  convert h3 using 1
  show L *ᵥ (NormedSpace.exp (t • L) *ᵥ v) = (L * NormedSpace.exp (t • L)) *ᵥ v
  rw [mulVec_mulVec]

/-- **Banded matrices.** If every row and every column of `R` has at most `b` nonzero entries
and all entries are bounded by `ε`, then `|uᵀRu| ≤ b ε |u|²`. -/
theorem banded_qf_le [DecidableEq ι] (R : Matrix ι ι ℝ) {b ε : ℝ}
    (hε : ∀ i j, |R i j| ≤ ε)
    (hrow : ∀ i, ((univ.filter fun j => R i j ≠ 0).card : ℝ) ≤ b)
    (hcol : ∀ j, ((univ.filter fun i => R i j ≠ 0).card : ℝ) ≤ b) (u : ι → ℝ) :
    |qf R u| ≤ b * ε * esq u := by
  rw [qf_eq_sum]
  have hε0 : ∀ i j, 0 ≤ ε := fun i j => le_trans (abs_nonneg _) (hε i j)
  -- `|u_i R_ij u_j| ≤ ½|R_ij| (u_i² + u_j²)`, and only nonzero entries contribute
  have hterm : ∀ i j, |u i * R i j * u j| ≤
      (if R i j ≠ 0 then ε else 0) * (u i ^ 2 + u j ^ 2) / 2 := by
    intro i j
    by_cases h : R i j = 0
    · simp [h]
    · simp only [h, ne_eq, not_false_eq_true, ite_true]
      rw [abs_mul, abs_mul]
      have h1 : |u i| * |u j| ≤ (u i ^ 2 + u j ^ 2) / 2 := by
        nlinarith [sq_nonneg (|u i| - |u j|), sq_abs (u i), sq_abs (u j)]
      have := hε i j
      calc |u i| * |R i j| * |u j| = |R i j| * (|u i| * |u j|) := by ring
        _ ≤ ε * ((u i ^ 2 + u j ^ 2) / 2) :=
          mul_le_mul this h1 (by positivity) (le_trans (abs_nonneg _) this)
        _ = _ := by ring
  calc |∑ i, ∑ j, u i * R i j * u j| ≤ ∑ i, ∑ j, |u i * R i j * u j| :=
        (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (if R i j ≠ 0 then ε else 0) * (u i ^ 2 + u j ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i, (∑ j, (if R i j ≠ 0 then ε else 0)) * u i ^ 2
          + ∑ j, (∑ i, (if R i j ≠ 0 then ε else 0)) * u j ^ 2) / 2 := by
        set c : ι → ι → ℝ := fun i j => if R i j ≠ 0 then ε else 0
        have e1 : ∑ i, ∑ j, c i j * (u i ^ 2 + u j ^ 2) / 2
            = (∑ i, ∑ j, c i j * u i ^ 2 + ∑ i, ∑ j, c i j * u j ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            exact Finset.sum_congr rfl fun j _ => by ring
        have e2 : ∑ i, ∑ j, c i j * u i ^ 2 = ∑ i, (∑ j, c i j) * u i ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
        have e3 : ∑ i, ∑ j, c i j * u j ^ 2 = ∑ j, (∑ i, c i j) * u j ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
        rw [e1, e2, e3]
    _ ≤ (∑ i, (b * ε) * u i ^ 2 + ∑ j, (b * ε) * u j ^ 2) / 2 := by
        gcongr with i _ j _
        · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hrow i) (hε0 i i)
        · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hcol j) (hε0 j j)
    _ = b * ε * esq u := by simp only [esq, ← Finset.mul_sum]; ring

/-- Norm equivalence for diagonal weights: if `c H ≤ H' ≤ C H`, the energies compare. -/
theorem wip_le_of_le {H H' : ι → ℝ} {C : ℝ} (h : ∀ i, H' i ≤ C * H i) (u : ι → ℝ) :
    wip H' u u ≤ C * wip H u u := by
  simp only [wip, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    have := mul_le_mul_of_nonneg_right (h i) (mul_self_nonneg (u i))
    nlinarith

end Meshfree.Stability
