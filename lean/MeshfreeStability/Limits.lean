import MeshfreeStability.Defects

/-!
# Section 9: limits of the energy method, and the parity of the order

* **Proposition 9.1** (lower bound for the numerical abscissa): `defect_inner`,
  `numerical_abscissa_lower_bound`.
* **Proposition 9.2** (exact energy identity, `K = 2`, nearest neighbours, periodic 1-D grid):
  (i) `nn_interp_slope`, `nn_rusanov_upwind`, `nn_slope_normal_eq`, `nn_conservation`;
  (ii) `nn_energy_identity`, `nn_Q_second_form`; (iii) `nn_uniform_nonneg`,
  `form_indefinite_of_ne`, `nn_Q_indefinite`, `two_periodic_det_neg`.
  The reduction of `𝒬` on admissible 2-periodic slopes to the `2×2` Hermitian Bloch form and the
  statement for `N ≤ 64` (computed) are not formalized.
* **Proposition 9.3** (parity): `cos_taylor_bound` (Taylor bound for `cos`, proved here),
  `parity_expansion`, `local_symbol_re`.
-/

open Finset Matrix Real

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

/-! ### Proposition 9.1 -/

section Obstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The defect density `d_j = H_j⁻¹ ∑_i H_i L_{ij}` (`d = L^{*_H} 1`). -/
noncomputable def defectDensity (H : ι → ℝ) (L : Matrix ι ι ℝ) : ι → ℝ :=
  fun j => (H j)⁻¹ * ∑ i, H i * L i j

/-- `⟨1, Lw⟩_H = ⟨d, w⟩_H`: the defect density is the rate of change of `∑ H_i U_i`. -/
theorem defect_inner (H : ι → ℝ) (hH : ∀ i, H i ≠ 0) (L : Matrix ι ι ℝ) (w : ι → ℝ) :
    wip H (fun _ => 1) (L *ᵥ w) = wip H (defectDensity H L) w := by
  simp only [wip, defectDensity, mulVec, dotProduct, mul_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc (H j), mul_inv_cancel₀ (hH j)]; ring

/-- **Proposition 9.1.** Let `L1 = 0`, `H > 0`, `|Ω|_H = ∑ H_i`, and `‖Lv‖_H ≤ Λ ‖v‖_H`
(`Λ > 0`). Then the vector `U = 1 + d/(2Λ)` satisfies
`⟨U, LU⟩_H ≥ ‖d‖²_H / (9 |Ω|_H Λ) · ‖U‖²_H` with `‖U‖_H > 0`; hence
`ω_H(L) ≥ ‖d‖²_H / (9 |Ω|_H Λ)`. -/
theorem numerical_abscissa_lower_bound [Nonempty ι] (H : ι → ℝ) (hH : ∀ i, 0 < H i)
    (L : Matrix ι ι ℝ) (hL1 : L *ᵥ (fun _ => 1) = 0) {Λ : ℝ} (hΛ : 0 < Λ)
    (hnorm : ∀ v, wip H (L *ᵥ v) (L *ᵥ v) ≤ Λ ^ 2 * wip H v v) :
    let d := defectDensity H L
    let U : ι → ℝ := fun i => 1 + d i / (2 * Λ)
    0 < wip H U U ∧
      wip H d d / (9 * (∑ i, H i) * Λ) * wip H U U ≤ wip H U (L *ᵥ U) := by
  intro d U
  have hH0 : ∀ i, 0 ≤ H i := fun i => (hH i).le
  have hHne : ∀ i, H i ≠ 0 := fun i => (hH i).ne'
  set Ω := ∑ i, H i
  set Dd := wip H d d
  have hΩ : 0 < Ω := Finset.sum_pos (fun i _ => hH i) Finset.univ_nonempty
  have hΩ' : wip H (fun _ => 1) (fun _ => 1) = Ω := by simp [wip, Ω]
  have hD0 : 0 ≤ Dd := wip_self_nonneg hH0 d
  -- `⟨1, d⟩_H = ⟨1, L1⟩_H = 0`
  have h1d : wip H (fun _ => 1) d = 0 := by
    have := defect_inner H hHne L (fun _ => 1)
    rw [hL1] at this
    have e0 : wip H (fun _ => 1) 0 = 0 := by simp [wip]
    rw [e0] at this
    rw [show wip H (fun _ => 1) d = wip H (defectDensity H L) (fun _ => 1) by
      simp only [wip, d]; exact Finset.sum_congr rfl fun i _ => by ring]
    exact this.symm
  -- `D ≤ Λ² Ω`
  have hDΛ : Dd ≤ Λ ^ 2 * Ω := by
    have e : Dd = wip H (fun _ => 1) (L *ᵥ d) := (defect_inner H hHne L d).symm
    have hcs := wip_le_sqrt_mul_sqrt hH0 (fun _ => 1) (L *ᵥ d)
    rw [← e, hΩ'] at hcs
    have h2 : Real.sqrt (wip H (L *ᵥ d) (L *ᵥ d)) ≤ Λ * Real.sqrt Dd := by
      calc Real.sqrt (wip H (L *ᵥ d) (L *ᵥ d)) ≤ Real.sqrt (Λ ^ 2 * Dd) := Real.sqrt_le_sqrt (hnorm d)
        _ = Λ * Real.sqrt Dd := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ.le]
    have h3 : Dd ≤ Real.sqrt Ω * (Λ * Real.sqrt Dd) :=
      hcs.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    have hsD := Real.sq_sqrt hD0
    have hsΩ := Real.sq_sqrt hΩ.le
    by_cases hz : Real.sqrt Dd = 0
    · have : Dd = 0 := by rw [← hsD, hz]; ring
      rw [this]; positivity
    · have hpos : 0 < Real.sqrt Dd := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      have : Real.sqrt Dd ≤ Real.sqrt Ω * Λ := by
        have h3' : Real.sqrt Dd * Real.sqrt Dd ≤ (Real.sqrt Ω * Λ) * Real.sqrt Dd := by
          rw [Real.mul_self_sqrt hD0]; linarith [h3]
        exact le_of_mul_le_mul_right h3' hpos
      calc Dd = Real.sqrt Dd ^ 2 := hsD.symm
        _ ≤ (Real.sqrt Ω * Λ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
        _ = Λ ^ 2 * Ω := by rw [mul_pow, hsΩ]; ring
  -- `|⟨d, Ld⟩_H| ≤ Λ D`
  have hdLd : -(Λ * Dd) ≤ wip H d (L *ᵥ d) := by
    have hcs := wip_le_sqrt_mul_sqrt hH0 (-d) (L *ᵥ d)
    have e1 : wip H (-d) (L *ᵥ d) = -wip H d (L *ᵥ d) := by simp [wip, Finset.sum_neg_distrib]
    have e2 : wip H (-d) (-d) = Dd := by simp [wip, Dd]
    rw [e1, e2] at hcs
    have h2 : Real.sqrt (wip H (L *ᵥ d) (L *ᵥ d)) ≤ Λ * Real.sqrt Dd := by
      calc Real.sqrt (wip H (L *ᵥ d) (L *ᵥ d)) ≤ Real.sqrt (Λ ^ 2 * Dd) := Real.sqrt_le_sqrt (hnorm d)
        _ = Λ * Real.sqrt Dd := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ.le]
    have := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg Dd)
    have hs : Real.sqrt Dd * (Λ * Real.sqrt Dd) = Λ * Dd := by
      rw [mul_left_comm, Real.mul_self_sqrt hD0]
    linarith
  -- expand `U = 1 + s d`, `s = 1/(2Λ)`
  set s := 1 / (2 * Λ)
  have hU : U = fun i => (fun _ => (1 : ℝ)) i + s * d i := by
    funext i; simp only [U, s]; ring
  have bil : ∀ a b c e : ι → ℝ, wip H (a + b) (c + e) = wip H a c + wip H a e + wip H b c + wip H b e := by
    intro a b c e; simp only [wip, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring
  have smul_l : ∀ (r : ℝ) (a b : ι → ℝ), wip H (r • a) b = r * wip H a b := by
    intro r a b; simp only [wip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have smul_r : ∀ (r : ℝ) (a b : ι → ℝ), wip H a (r • b) = r * wip H a b := by
    intro r a b; simp only [wip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hU' : U = (fun _ => (1 : ℝ)) + s • d := by rw [hU]; rfl
  have symm : ∀ a b : ι → ℝ, wip H a b = wip H b a := by
    intro a b; simp only [wip]; exact Finset.sum_congr rfl fun i _ => by ring
  have hUU : wip H U U = Ω + s ^ 2 * Dd := by
    rw [hU', bil, smul_l, smul_r, smul_l, smul_r, h1d, symm d, h1d, hΩ']; ring
  have hLU : wip H U (L *ᵥ U) = s * Dd + s ^ 2 * wip H d (L *ᵥ d) := by
    have hLUv : L *ᵥ U = s • (L *ᵥ d) := by rw [hU', mulVec_add, hL1, zero_add, mulVec_smul]
    have addl : ∀ a b c : ι → ℝ, wip H (a + b) c = wip H a c + wip H b c := by
      intro a b c; simp only [wip, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    have hdd : wip H (defectDensity H L) d = Dd := rfl
    rw [hLUv, smul_r, hU', addl, smul_l, defect_inner H hHne L d, hdd]; ring
  have hs : s = 1 / (2 * Λ) := rfl
  refine ⟨by rw [hUU]; positivity, ?_⟩
  rw [hUU, hLU]
  -- `s D + s² ⟨d,Ld⟩ ≥ D/(4Λ)` and `Ω + s² D ≤ (9/4) Ω`
  have hnum : Dd / (4 * Λ) ≤ s * Dd + s ^ 2 * wip H d (L *ᵥ d) := by
    have : s ^ 2 * (-(Λ * Dd)) ≤ s ^ 2 * wip H d (L *ᵥ d) :=
      mul_le_mul_of_nonneg_left hdLd (sq_nonneg _)
    have e : s * Dd + s ^ 2 * (-(Λ * Dd)) = Dd / (4 * Λ) := by rw [hs]; field_simp; ring
    linarith
  have hden : Ω + s ^ 2 * Dd ≤ 9 / 4 * Ω := by
    have : s ^ 2 * Dd ≤ s ^ 2 * (Λ ^ 2 * Ω) := mul_le_mul_of_nonneg_left hDΛ (sq_nonneg _)
    have e : s ^ 2 * (Λ ^ 2 * Ω) = Ω / 4 := by rw [hs]; field_simp; ring
    linarith
  calc Dd / (9 * Ω * Λ) * (Ω + s ^ 2 * Dd) ≤ Dd / (9 * Ω * Λ) * (9 / 4 * Ω) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ = Dd / (4 * Λ) := by field_simp
    _ ≤ _ := hnum

end Obstruction

/-! ### Proposition 9.2 -/

section NearestNeighbour

variable {N : ℕ} [NeZero N]

local notation "Gr" => ZMod N

/-- Slope on gap `i`: `σ_i = (U_{i+1} - U_i)/g_i`. -/
noncomputable def nnSlope (g U : Gr → ℝ) (i : Gr) : ℝ := (U (i + 1) - U i) / g i

/-- Weighted least-squares reconstruction slope `γ_i` of `eq:fv`. -/
noncomputable def nnGamma (g wp wm σ : Gr → ℝ) (i : Gr) : ℝ :=
  (wp i * g i ^ 2 * σ i + wm i * g (i - 1) ^ 2 * σ (i - 1)) / (wp i * g i ^ 2 + wm i * g (i - 1) ^ 2)

/-- `m_i` of `eq:nnQ`. -/
noncomputable def nnM (g wp wm : Gr → ℝ) (i : Gr) : ℝ :=
  wm i * g (i - 1) ^ 2 * g i ^ 2 / (wp i * g i ^ 2 + wm i * g (i - 1) ^ 2)

/-- The right-hand side `V_i dU_i/dt = -a(U_{i,i+1} - U_{i-1,i})` of `eq:fv`. -/
noncomputable def nnRhs (a : ℝ) (g wp wm U : Gr → ℝ) (i : Gr) : ℝ :=
  let σ := nnSlope g U;
  let F := (fun k => U k + (1 / 2) * g k * nnGamma g wp wm σ k);
  -a * (F i - F (i - 1))

/-- The quadratic form `𝒬(σ) = ∑ m_i σ_i (σ_i - σ_{i-1})`. -/
noncomputable def nnQ (m σ : Gr → ℝ) : ℝ := ∑ i, m i * σ i * (σ i - σ (i - 1))

theorem sum_sub_one (f : Gr → ℝ) : ∑ i, f (i - 1) = ∑ i, f i := by
  simpa [sub_eq_add_neg] using sum_shift f (-1 : Gr)

theorem sum_add_one (f : Gr → ℝ) : ∑ i, f (i + 1) = ∑ i, f i := sum_shift f 1

/-- **Proposition 9.2(i), derivative weights.** The degree-one fit with constant term through the
two neighbours has slope `(U_{i+1} - U_{i-1})/(g_{i-1} + g_i)`, i.e. `c_{i,i±1} = ±1/(g_{i-1}+g_i)`,
and then `V_i c_{i,i+1} = ½ = -V_{i+1} c_{i+1,i}`. -/
theorem nn_interp_slope {gm gp Um U0 Up b0 b1 : ℝ} (hg : 0 < gm + gp)
    (hm : b0 + b1 * (-gm) = Um - U0) (hp : b0 + b1 * gp = Up - U0) :
    b1 = (Up - Um) / (gm + gp) ∧ (gm + gp) / 2 * (1 / (gm + gp)) = 1 / 2 := by
  constructor
  · rw [eq_div_iff hg.ne']; linarith
  · field_simp

/-- **Proposition 9.2(i), the upwind reduction.** For `F(U) = aU`, `s = a > 0`, the Rusanov
flux of [A] with `σ = +1` (right neighbour) is `a U_{ij}`, with `σ = -1` (left neighbour) it is
`a U_{ji}`. -/
theorem nn_rusanov_upwind (a x y : ℝ) :
    rusanov (fun u => a * u) a 1 x y = a * x ∧ rusanov (fun u => a * u) a (-1) x y = a * y := by
  constructor <;> simp only [rusanov, smul_eq_mul] <;> ring

/-- **Proposition 9.2(i), the reconstruction slope.** `γ_i` solves the weighted normal equation
of the fit through `U_i` with the data `±g σ` on the two sides (so it is the weighted
least-squares slope). -/
theorem nn_slope_normal_eq {gp gm wp wm sp sm : ℝ} (hden : wp * gp ^ 2 + wm * gm ^ 2 ≠ 0) :
    let γ := (wp * gp ^ 2 * sp + wm * gm ^ 2 * sm) / (wp * gp ^ 2 + wm * gm ^ 2)
    wp * (γ * gp - gp * sp) * gp + wm * (γ * (-gm) - (-gm) * sm) * (-gm) = 0 := by
  intro γ
  simp only [γ]; field_simp; ring

/-- **Proposition 9.2(i), conservation.** `∑_i V_i dU_i/dt = 0`, i.e. `L^{*_V} 1 = 0`. -/
theorem nn_conservation (a : ℝ) (g wp wm U : Gr → ℝ) : ∑ i, nnRhs a g wp wm U i = 0 := by
  simp only [nnRhs, mul_sub, Finset.sum_sub_distrib]
  rw [sum_sub_one (fun k => -a * (U k + 1 / 2 * g k * nnGamma g wp wm (nnSlope g U) k))]
  ring

/-- **Proposition 9.2(ii), `eq:nnQ`.** For positive gaps and weights,
`2 ∑_i U_i · (V_i dU_i/dt) = d/dt ‖U‖²_V = -a 𝒬(σ)`. -/
theorem nn_energy_identity (a : ℝ) (g wp wm U : Gr → ℝ) (hg : ∀ i, 0 < g i)
    (hwp : ∀ i, 0 < wp i) (hwm : ∀ i, 0 < wm i) :
    2 * ∑ i, U i * nnRhs a g wp wm U i = -a * nnQ (nnM g wp wm) (nnSlope g U) := by
  set σ := nnSlope g U
  set γ := nnGamma g wp wm σ
  have hσ : ∀ i, U (i + 1) - U i = g i * σ i := fun i => by
    simp only [σ, nnSlope]; field_simp [(hg i).ne']
  have hden : ∀ i, 0 < wp i * g i ^ 2 + wm i * g (i - 1) ^ 2 := fun i => by
    have := hwp i; have := hwm i; have := hg i; have := hg (i - 1); positivity
  -- summation by parts
  have e1 : ∑ i, U i * nnRhs a g wp wm U i
      = a * ∑ i, (U i + (1 / 2) * g i * γ i) * (g i * σ i) := by
    simp only [nnRhs]
    have : ∑ i, U i * (-a * ((U i + 1 / 2 * g i * γ i) - (U (i - 1) + 1 / 2 * g (i - 1) * γ (i - 1))))
        = -a * (∑ i, U i * (U i + 1 / 2 * g i * γ i)
          - ∑ i, U (i + 1) * (U i + 1 / 2 * g i * γ i)) := by
      rw [← sum_sub_one (fun i => U (i + 1) * (U i + 1 / 2 * g i * γ i))]
      simp only [sub_add_cancel, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hσ]; ring
  have e2 : 2 * ∑ i, U i * (g i * σ i) = -∑ i, g i ^ 2 * σ i ^ 2 := by
    have : ∀ i, U i * (g i * σ i) = U i * U (i + 1) - U i ^ 2 := fun i => by rw [← hσ]; ring
    simp only [this, Finset.sum_sub_distrib]
    have h2 : ∑ i, g i ^ 2 * σ i ^ 2 = ∑ i, (U (i + 1) ^ 2 - 2 * (U i * U (i + 1)) + U i ^ 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show g i ^ 2 * σ i ^ 2 = (g i * σ i) ^ 2 by ring, ← hσ]; ring
    rw [h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_add_one (fun i => U i ^ 2),
      ← Finset.mul_sum]
    ring
  have e3 : ∀ i, g i ^ 2 * σ i ^ 2 - g i ^ 2 * γ i * σ i = nnM g wp wm i * σ i * (σ i - σ (i - 1)) := by
    intro i
    simp only [γ, nnGamma, nnM]
    set D := wp i * g i ^ 2 + wm i * g (i - 1) ^ 2 with hDdef
    have hD : D ≠ 0 := (hden i).ne'
    field_simp
    try rw [hDdef]
    ring
  rw [e1]
  have : 2 * (a * ∑ i, (U i + 1 / 2 * g i * γ i) * (g i * σ i))
      = a * (2 * ∑ i, U i * (g i * σ i)) + a * ∑ i, g i ^ 2 * γ i * σ i := by
    have h : ∀ i, (U i + 1 / 2 * g i * γ i) * (g i * σ i)
        = U i * (g i * σ i) + (1 / 2) * (g i ^ 2 * γ i * σ i) := fun i => by ring
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  rw [this, e2, nnQ]
  simp only [← e3, Finset.sum_sub_distrib]
  ring

/-- **Proposition 9.2(ii), the second form of `𝒬`.** -/
theorem nn_Q_second_form (m σ : Gr → ℝ) :
    nnQ m σ = (1 / 2) * ∑ i, m i * (σ i - σ (i - 1)) ^ 2
      + (1 / 2) * ∑ i, (m i - m (i + 1)) * σ i ^ 2 := by
  simp only [nnQ]
  have h : ∑ i, m (i + 1) * σ i ^ 2 = ∑ i, m i * σ (i - 1) ^ 2 := by
    rw [← sum_sub_one (fun i => m (i + 1) * σ i ^ 2)]; simp
  have e : ∑ i, (m i - m (i + 1)) * σ i ^ 2 = ∑ i, m i * σ i ^ 2 - ∑ i, m i * σ (i - 1) ^ 2 := by
    rw [← h, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  calc ∑ i, m i * σ i * (σ i - σ (i - 1))
      = ∑ i, ((1 / 2) * (m i * (σ i - σ (i - 1)) ^ 2)
          + ((1 / 2) * (m i * σ i ^ 2) - (1 / 2) * (m i * σ (i - 1) ^ 2))) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring

/-- **Proposition 9.2(iii), uniform grids.** If `m` is constant, `𝒬 = (m/2) ∑ (σ_i - σ_{i-1})² ≥ 0`
(Fromm's scheme is contractive in `‖·‖_V`). -/
theorem nn_uniform_nonneg (m0 : ℝ) (hm0 : 0 ≤ m0) (σ : Gr → ℝ) :
    nnQ (fun _ => m0) σ = m0 / 2 * ∑ i, (σ i - σ (i - 1)) ^ 2 ∧ 0 ≤ nnQ (fun _ => m0) σ := by
  have h := nn_Q_second_form (fun _ => m0) σ
  simp only [sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at h
  rw [h, ← Finset.mul_sum]
  refine ⟨by ring, ?_⟩
  have : 0 ≤ ∑ i, (σ i - σ (i - 1)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

/-- A quadratic form vanishing at `x` but with nonzero linear term at `x` takes negative values:
`q(x + s w) = 2 s β + s² q(w)` with `β ≠ 0`. -/
theorem form_indefinite_of_ne (qw β : ℝ) (hβ : β ≠ 0) :
    ∃ s : ℝ, 2 * s * β + s ^ 2 * qw < 0 := by
  refine ⟨-β / (|qw| + 1), ?_⟩
  have hpos : 0 < |qw| + 1 := by positivity
  have e : 2 * (-β / (|qw| + 1)) * β + (-β / (|qw| + 1)) ^ 2 * qw
      = -(β ^ 2 / (|qw| + 1)) * (2 - qw / (|qw| + 1)) := by field_simp; ring
  rw [e]
  have h1 : 0 < β ^ 2 / (|qw| + 1) := by positivity
  have h2 : qw / (|qw| + 1) < 1 := by
    rw [div_lt_one hpos]; linarith [le_abs_self qw]
  nlinarith

/-- **Proposition 9.2(iii), indefiniteness on `ℝ^N`.** If `m` is not constant (some
`m_i ≠ m_{i+1}`), `𝒬` takes negative values: `𝒬(1) = 0` and the linear term of `𝒬` at `1` in
direction `w` is `½∑ (m_i - m_{i+1}) w_i`, which is nonzero for `w = T1`. -/
theorem nn_Q_indefinite (m : Gr → ℝ) (hm : ∃ i, m i ≠ m (i + 1)) :
    ∃ σ : Gr → ℝ, nnQ m σ < 0 := by
  set w : Gr → ℝ := fun i => (m i - m (i + 1)) / 2
  set β : ℝ := ∑ i, (m i - m (i + 1)) / 2 * w i
  have hβ : β ≠ 0 := by
    obtain ⟨i0, hi0⟩ := hm
    have : 0 < β := by
      have hterm : ∀ i, (m i - m (i + 1)) / 2 * w i = ((m i - m (i + 1)) / 2) ^ 2 := fun i => by
        simp only [w]; ring
      simp only [β, hterm]
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, Finset.mem_univ _, ?_⟩
      have : m i0 - m (i0 + 1) ≠ 0 := sub_ne_zero.2 hi0
      positivity
    exact this.ne'
  obtain ⟨s, hs⟩ := form_indefinite_of_ne (nnQ m w) β hβ
  refine ⟨fun i => 1 + s * w i, ?_⟩
  have e : nnQ m (fun i => 1 + s * w i) = 2 * s * β + s ^ 2 * nnQ m w := by
    simp only [nnQ, β]
    have h1 : ∑ i, m i * (1 + s * w i) * ((1 + s * w i) - (1 + s * w (i - 1)))
        = s * ∑ i, m i * (w i - w (i - 1)) + s ^ 2 * ∑ i, m i * w i * (w i - w (i - 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, m i * (w i - w (i - 1)) = 2 * ∑ i, (m i - m (i + 1)) / 2 * w i := by
      have : ∑ i, m i * w (i - 1) = ∑ i, m (i + 1) * w i := by
        rw [← sum_sub_one (fun i => m (i + 1) * w i)]; simp
      have e : ∑ i, m i * (w i - w (i - 1)) = ∑ i, m i * w i - ∑ i, m i * w (i - 1) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, this, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2]; ring
  rw [e]; exact hs

/-- **Proposition 9.2(iii), the 2-periodic determinant.** For `m_e ≠ m_o`, the determinant
`-¼(m_e - m_o)² + ½ m_e m_o (1 - cos θ)` of the Bloch form is negative at `θ = 4π/N` for all
large `N`. (Stated with `4π/(n+1)`, i.e. `N = n + 1`.) -/
theorem two_periodic_det_neg {me mo : ℝ} (hme : 0 < me) (hmo : 0 < mo) (hne : me ≠ mo) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      -(1 / 4) * (me - mo) ^ 2 + (1 / 2) * me * mo * (1 - cos (4 * π / (n + 1))) < 0 := by
  have hd : 0 < (me - mo) ^ 2 := by have := sub_ne_zero.2 hne; positivity
  -- `1 - cos x ≤ x²/2`
  obtain ⟨N0, hN0⟩ := exists_nat_gt (16 * π ^ 2 * me * mo / (me - mo) ^ 2)
  refine ⟨N0, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hcos : 1 - cos (4 * π / (n + 1)) ≤ (4 * π / (n + 1)) ^ 2 / 2 := by
    linarith [one_sub_sq_div_two_le_cos (x := 4 * π / (n + 1))]
  have hbig : 16 * π ^ 2 * me * mo / (me - mo) ^ 2 < n + 1 := by
    have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ hd] at hbig
  have hmm : 0 < me * mo := mul_pos hme hmo
  have : (1 / 2) * me * mo * (1 - cos (4 * π / (n + 1)))
      ≤ (1 / 2) * me * mo * ((4 * π / (n + 1)) ^ 2 / 2) := by
    have := mul_le_mul_of_nonneg_left hcos (by positivity : (0 : ℝ) ≤ (1 / 2) * me * mo)
    linarith
  have e : (1 / 2) * me * mo * ((4 * π / (n + 1)) ^ 2 / 2) = 4 * π ^ 2 * me * mo / (n + 1) ^ 2 := by
    field_simp; ring
  rw [e] at this
  have h1 : 4 * π ^ 2 * me * mo / (n + 1) ^ 2 < (1 / 4) * (me - mo) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have hn2 : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h3 : (n + 1) * (16 * π ^ 2 * me * mo) < (n + 1) * ((n + 1) * (me - mo) ^ 2) :=
      mul_lt_mul_of_pos_left hbig hn1
    have h4 : 16 * π ^ 2 * me * mo ≤ (n + 1) * (16 * π ^ 2 * me * mo) :=
      le_mul_of_one_le_left (by positivity) hn2
    nlinarith
  linarith

end NearestNeighbour

/-! ### Proposition 9.3 -/

section Parity

/-- Taylor polynomial of `cos` of degree `2k`. -/
noncomputable def cosT (k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range (k + 1), (-1) ^ r * x ^ (2 * r) / (2 * r).factorial

/-- Taylor polynomial of `sin` of degree `2k - 1`. -/
noncomputable def sinT (k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range k, (-1) ^ r * x ^ (2 * r + 1) / (2 * r + 1).factorial

theorem hasDerivAt_cosT (k : ℕ) (x : ℝ) : HasDerivAt (cosT k) (-sinT k x) x := by
  unfold cosT sinT
  induction k with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, mul_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, range_zero, sum_empty, neg_zero]
    exact hasDerivAt_const x 1
  | succ k ih =>
    simp only [Finset.sum_range_succ (n := k + 1)]
    rw [Finset.sum_range_succ (n := k), neg_add]
    refine ih.add ?_
    have h := ((hasDerivAt_pow (2 * (k + 1)) x).const_mul ((-1 : ℝ) ^ (k + 1))).div_const
      ((2 * (k + 1)).factorial : ℝ)
    convert h using 1
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ]
    push_cast
    try rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem hasDerivAt_sinT (k : ℕ) (x : ℝ) : HasDerivAt (sinT (k + 1)) (cosT k x) x := by
  unfold cosT sinT
  induction k with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, mul_zero, Nat.factorial_one,
      Nat.cast_one, div_one, one_mul, pow_one, Nat.factorial_zero]
    exact hasDerivAt_id x
  | succ k ih =>
    simp only [Finset.sum_range_succ (n := k + 1)]
    refine ih.add ?_
    have h := ((hasDerivAt_pow (2 * (k + 1) + 1) x).const_mul ((-1 : ℝ) ^ (k + 1))).div_const
      ((2 * (k + 1) + 1).factorial : ℝ)
    convert h using 1
    rw [Nat.factorial_succ]
    push_cast
    try rw [show 2 * (k + 1) + 1 - 1 = 2 * (k + 1) by omega]
    field_simp

/-- Integration step: `f(0) = 0` and `|f'| ≤ x^n/n!` on `[0,∞)` give `|f| ≤ x^{n+1}/(n+1)!`. -/
theorem integrate_bound {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0) (n : ℕ)
    (hb : ∀ x, 0 ≤ x → |f' x| ≤ x ^ n / n.factorial) :
    ∀ x, 0 ≤ x → |f x| ≤ x ^ (n + 1) / (n + 1).factorial := by
  have hP : ∀ x, HasDerivAt (fun y => y ^ (n + 1) / ((n + 1).factorial : ℝ))
      (x ^ n / n.factorial) x := by
    intro x
    have := (hasDerivAt_pow (n + 1) x).div_const ((n + 1).factorial : ℝ)
    convert this using 1
    rw [Nat.factorial_succ]; push_cast
    try rw [show n + 1 - 1 = n by omega]
    field_simp
  have mono : ∀ g g' : ℝ → ℝ, (∀ x, HasDerivAt g (g' x) x) → (∀ x, 0 ≤ x → 0 ≤ g' x) →
      MonotoneOn g (Set.Ici 0) := by
    intro g g' hg hg'
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => hg' x ?_)
    rw [interior_Ici] at hx; exact le_of_lt hx
  have m1 := mono (fun y => y ^ (n + 1) / ((n + 1).factorial : ℝ) - f y)
    (fun x => x ^ n / n.factorial - f' x) (fun x => (hP x).sub (hf x))
    (fun x hx => by linarith [le_abs_self (f' x), hb x hx])
  have m2 := mono (fun y => y ^ (n + 1) / ((n + 1).factorial : ℝ) + f y)
    (fun x => x ^ n / n.factorial + f' x) (fun x => (hP x).add (hf x))
    (fun x hx => by linarith [neg_abs_le (f' x), hb x hx])
  intro x hx
  have a1 := m1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  have a2 := m2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [h0, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_div, sub_zero, add_zero] at a1 a2
  rw [abs_le]; constructor <;> linarith

/-- **Taylor bound for `cos`** (all orders): `|cos x - T_{2k}(x)| ≤ |x|^{2k+2}/(2k+2)!` and
`|sin x - T_{2k-1}(x)| ≤ x^{2k+1}/(2k+1)!` for `x ≥ 0`. -/
theorem cos_sin_taylor (k : ℕ) :
    (∀ x, 0 ≤ x → |sin x - sinT k x| ≤ x ^ (2 * k + 1) / (2 * k + 1).factorial) ∧
    (∀ x, 0 ≤ x → |cos x - cosT k x| ≤ x ^ (2 * k + 2) / (2 * k + 2).factorial) := by
  induction k with
  | zero =>
    have hs : ∀ x, 0 ≤ x → |sin x - sinT 0 x| ≤ x ^ (2 * 0 + 1) / (2 * 0 + 1).factorial := by
      intro x hx
      simp only [sinT, range_zero, sum_empty, sub_zero, mul_zero, zero_add, pow_one,
        Nat.factorial_one, Nat.cast_one, div_one]
      exact (abs_sin_le_abs).trans (le_of_eq (abs_of_nonneg hx))
    refine ⟨hs, ?_⟩
    have := integrate_bound (f := fun x => cos x - cosT 0 x) (f' := fun x => -(sin x - sinT 0 x))
      (fun x => (hasDerivAt_cos x).sub (hasDerivAt_cosT 0 x) |>.congr_deriv (by ring))
      (by simp [cosT]) 1 (fun x hx => by rw [abs_neg]; simpa using hs x hx)
    simpa using this
  | succ k ih =>
    have hs := integrate_bound (f := fun x => sin x - sinT (k + 1) x)
      (f' := fun x => cos x - cosT k x)
      (fun x => (hasDerivAt_sin x).sub (hasDerivAt_sinT k x)) (by simp [sinT])
      (2 * k + 2) ih.2
    have hs' : ∀ x, 0 ≤ x → |sin x - sinT (k + 1) x| ≤
        x ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1).factorial := by
      intro x hx; have := hs x hx
      rwa [show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring] at this
    refine ⟨hs', ?_⟩
    have := integrate_bound (f := fun x => cos x - cosT (k + 1) x)
      (f' := fun x => -(sin x - sinT (k + 1) x))
      (fun x => (hasDerivAt_cos x).sub (hasDerivAt_cosT (k + 1) x) |>.congr_deriv (by ring))
      (by simp [cosT, Finset.sum_range_succ', zero_pow]) (2 * (k + 1) + 1)
      (fun x hx => by rw [abs_neg]; exact hs' x hx)
    intro x hx
    have := this x hx
    rwa [show 2 * (k + 1) + 1 + 1 = 2 * (k + 1) + 2 by ring] at this

theorem cosT_neg (k : ℕ) (x : ℝ) : cosT k (-x) = cosT k x := by
  simp only [cosT]
  exact Finset.sum_congr rfl fun r _ => by rw [show 2 * r = 2 * r from rfl, pow_mul, pow_mul,
    neg_sq]

theorem cos_taylor_bound (k : ℕ) (x : ℝ) :
    |cos x - cosT k x| ≤ |x| ^ (2 * k + 2) / (2 * k + 2).factorial := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact (cos_sin_taylor k).2 x hx
  · have := (cos_sin_taylor k).2 (-x) (by linarith)
    rw [cos_neg, cosT_neg, ← abs_of_nonpos hx] at this
    exact this

/-- **Proposition 9.3 (parity), the expansion `eq:parity`.** If the row annihilates the even
monomials of degree `< 2k` (`∑_j L_j φ_j^{2r} = 0` for `r < k`; for the scheme this is
Proposition 4.2 of [A] applied to `p(y) = (θ·y/h)^{2r} ∈ Π_{K-1}`, whose gradient vanishes at `0`,
where `2k` is the smallest even integer `≥ K`), then
`|∑_j L_j cos φ_j - (-1)^k/(2k)! ∑_j L_j φ_j^{2k}| ≤ ∑_j |L_j| |φ_j|^{2k+2}/(2k+2)!`. -/
theorem parity_expansion {J : Type*} [Fintype J] (L φ : J → ℝ) (k : ℕ)
    (hann : ∀ r < k, ∑ j, L j * φ j ^ (2 * r) = 0) :
    |∑ j, L j * cos (φ j) - (-1) ^ k / (2 * k).factorial * ∑ j, L j * φ j ^ (2 * k)|
      ≤ ∑ j, |L j| * (|φ j| ^ (2 * k + 2) / (2 * k + 2).factorial) := by
  have hT : ∑ j, L j * cosT k (φ j) = (-1) ^ k / (2 * k).factorial * ∑ j, L j * φ j ^ (2 * k) := by
    simp only [cosT, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_range_succ]
    have hz : ∑ r ∈ range k, ∑ j, L j * ((-1) ^ r * φ j ^ (2 * r) / (2 * r).factorial) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have := hann r (Finset.mem_range.1 hr)
      have e : ∑ j, L j * ((-1) ^ r * φ j ^ (2 * r) / (2 * r).factorial)
          = (-1) ^ r / (2 * r).factorial * ∑ j, L j * φ j ^ (2 * r) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e, this, mul_zero]
    rw [hz, zero_add]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [← hT, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (cos_taylor_bound k (φ j)) (abs_nonneg _)

/-- The real part of the local symbol: `Re ∑_j L_j e^{iφ_j} = ∑_j L_j cos φ_j` (`L` real). -/
theorem local_symbol_re {J : Type*} [Fintype J] (L φ : J → ℝ) :
    (∑ j, (L j : ℂ) * Complex.exp (φ j * Complex.I)).re = ∑ j, L j * cos (φ j) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Proposition 9.3, the `O(|θ|^{2k+2}/h)` remainder.** With `|φ_j| ≤ 2κ|θ|` (two stencil
layers) and `∑_j |L_j| ≤ A/h` (Lemma 3.5 of [A]), the remainder in `eq:parity` is at most
`A (2κ|θ|)^{2k+2} / ((2k+2)! h)`. -/
theorem parity_remainder {J : Type*} [Fintype J] (L φ : J → ℝ) (k : ℕ) {κ θ A h : ℝ}
    (hφ : ∀ j, |φ j| ≤ 2 * κ * |θ|) (hL : ∑ j, |L j| ≤ A / h) :
    ∑ j, |L j| * (|φ j| ^ (2 * k + 2) / (2 * k + 2).factorial)
      ≤ A / h * ((2 * κ * |θ|) ^ (2 * k + 2) / (2 * k + 2).factorial) := by
  calc ∑ j, |L j| * (|φ j| ^ (2 * k + 2) / (2 * k + 2).factorial)
      ≤ ∑ j, |L j| * ((2 * κ * |θ|) ^ (2 * k + 2) / (2 * k + 2).factorial) := by
        gcongr with j _
        exact hφ j
    _ = (∑ j, |L j|) * ((2 * κ * |θ|) ^ (2 * k + 2) / (2 * k + 2).factorial) := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right hL ?_
        have : 0 ≤ (2 * κ * |θ|) ^ (2 * k + 2) := by
          rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; positivity
        positivity

end Parity

end Meshfree.Stability
