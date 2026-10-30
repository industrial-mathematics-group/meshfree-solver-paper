import MeshfreeStability.Nonlinear

/-!
# Section 4: the first-order scheme on arbitrary clouds (linear advection)

* **Theorem 4.1** (Markov structure):
  (i) `qcoef_nonneg`, `genMat_mulVec`, `genMat_one`, `markov_max_principle`;
  (ii) `stationary_conserved` (existence and uniqueness of `π` from irreducibility,
       Perron–Frobenius, are not formalized: `π` enters as a hypothesis);
  (iii) `markov_energy_identity`, `markov_L2_contraction`;
  (iv) `euler_step_contraction_p`, `euler_step_max`, `rk_contraction_p`;
  (v) `markov_volume_bound`.
* **Proposition 4.3** (truncation error): `truncation_identity`, `beta_zero_of_symmetric`.
* **Theorem 4.4** (drift): `corrector_identity`, `drift_error_bound`.
* **Proposition 4.5** (moment-corrected dissipation): `moment_corrected_admissible`,
  `moment_corrected_first_moment`.
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Theorem 4.1 -/

/-- The first-order aligned coefficient `q = ∑_d (|a_d||c_d| - a_d c_d)` of `eq:Q`. -/
def qcoef {D : ℕ} (a c : Fin D → ℝ) : ℝ := ∑ d, (|a d| * |c d| - a d * c d)

/-- **Theorem 4.1(i), first part.** `q_{ij} ≥ 0` for any weights and velocity. -/
theorem qcoef_nonneg {D : ℕ} (a c : Fin D → ℝ) : 0 ≤ qcoef a c :=
  Finset.sum_nonneg fun d _ => by rw [← abs_mul]; linarith [le_abs_self (a d * c d)]

/-- The operator `(QU)_i = ∑_j q_{ij} (U_j - U_i)` as a matrix. -/
def genMat (q : ι → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => q i j - if i = j then ∑ k, q i k else 0

theorem genMat_mulVec (q : ι → ι → ℝ) (U : ι → ℝ) (i : ι) :
    (genMat q *ᵥ U) i = ∑ j, q i j * (U j - U i) := by
  simp only [genMat, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_sub, Finset.sum_mul]

/-- `Q 1 = 0`. -/
theorem genMat_one (q : ι → ι → ℝ) : genMat q *ᵥ (fun _ => 1) = 0 := by
  ext i; simp [genMat_mulVec]

/-- Stationarity `πᵀQ = 0`, written out: `∑_i π_i q_{ij} = π_j ∑_k q_{jk}`. -/
def Stationary (q : ι → ι → ℝ) (π : ι → ℝ) : Prop :=
  ∀ j, ∑ i, π i * q i j = π j * ∑ k, q j k

theorem stationary_iff (q : ι → ι → ℝ) (π : ι → ℝ) :
    Stationary q π ↔ vecMul π (genMat q) = 0 := by
  constructor
  · intro h; ext j
    simp only [vecMul, dotProduct, genMat, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Pi.zero_apply]
    rw [h j]
    simp [Finset.sum_ite_eq']
  · intro h j
    have := congrFun h j
    simp only [vecMul, dotProduct, genMat, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Pi.zero_apply] at this
    simp [Finset.sum_ite_eq'] at this
    linarith

/-- Derivative of `(max x 0)²`. -/
theorem hasDerivAt_posPart_sq (x : ℝ) :
    HasDerivAt (fun y => max y 0 ^ 2) (2 * max x 0) x := by
  rcases lt_trichotomy x 0 with h | h | h
  · have : (fun y : ℝ => max y 0 ^ 2) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      simp [max_eq_right (le_of_lt (Set.mem_Iio.1 hy))]
    rw [max_eq_right h.le, mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq this
  · subst h
    simp only [max_self, mul_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, smul_zero]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_
      (Asymptotics.isLittleO_pow_id (by norm_num))
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    rcases le_total y 0 with hy | hy
    · rw [max_eq_right hy]; nlinarith [sq_nonneg y]
    · rw [max_eq_left hy]
  · have : (fun y : ℝ => max y 0 ^ 2) =ᶠ[nhds x] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      simp [max_eq_left (le_of_lt (Set.mem_Ioi.1 hy))]
    rw [max_eq_left h.le]
    simpa using (hasDerivAt_pow 2 x).congr_of_eventuallyEq this

/-- Upper half of the maximum principle. -/
theorem markov_upper (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) {U : ℝ → ι → ℝ}
    (hU : ∀ t, HasDerivAt U (genMat q *ᵥ U t) t) {M : ℝ} (h0 : ∀ i, U 0 i ≤ M)
    {t : ℝ} (ht : 0 ≤ t) (i : ι) : U t i ≤ M := by
  set a : ℝ → ι → ℝ := fun s i => max (U s i - M) 0
  set E : ℝ → ℝ := fun s => ∑ i, a s i ^ 2
  set K : ℝ := ∑ i, ∑ j, q i j
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hq i j
  have hE : ∀ s, HasDerivAt E (∑ i, 2 * a s i * (genMat q *ᵥ U s) i) s := by
    intro s
    have hi : ∀ i, HasDerivAt (fun s => a s i ^ 2) (2 * a s i * (genMat q *ᵥ U s) i) s := by
      intro i
      have h1 := ((hasDerivAt_pi.1 (hU s)) i).sub_const M
      have h2 := (hasDerivAt_posPart_sq (U s i - M)).comp s h1
      exact h2
    exact HasDerivAt.fun_sum fun i _ => hi i
  -- `E' ≤ K E`
  have hEK : ∀ s, ∑ i, 2 * a s i * (genMat q *ᵥ U s) i ≤ K * E s := by
    intro s
    have hterm : ∀ i, 2 * a s i * (genMat q *ᵥ U s) i ≤ ∑ j, q i j * a s j ^ 2 := by
      intro i
      rw [genMat_mulVec]
      by_cases hai : a s i = 0
      · rw [hai]; simp only [mul_zero, zero_mul]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hq i j) (sq_nonneg _)
      · have hpos : 0 < a s i := lt_of_le_of_ne (le_max_right _ _) (Ne.symm hai)
        have hai' : a s i = U s i - M := by
          simp only [a] at hpos ⊢; rcases le_total (U s i - M) 0 with h | h
          · rw [max_eq_right h] at hpos; exact absurd hpos (lt_irrefl 0)
          · rw [max_eq_left h]
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        have hj : U s j - U s i ≤ a s j - a s i := by
          rw [hai']; have := le_max_left (U s j - M) 0; simp only [a] at this ⊢; linarith
        have := mul_le_mul_of_nonneg_left hj (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * a s i) (hq i j))
        have h3 := mul_nonneg (hq i j) (sq_nonneg (a s i - a s j))
        have h4 := mul_nonneg (hq i j) (sq_nonneg (a s i))
        nlinarith [this, h3, h4]
    calc ∑ i, 2 * a s i * (genMat q *ᵥ U s) i ≤ ∑ i, ∑ j, q i j * a s j ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ∑ i, ∑ j, q i j * E s := by
          gcongr with i _ j _
          · exact hq i j
          · exact Finset.single_le_sum (f := fun k => a s k ^ 2) (fun k _ => sq_nonneg _)
              (Finset.mem_univ j)
      _ = K * E s := by simp only [K, Finset.sum_mul]
  -- Grönwall with `E 0 = 0`
  set f : ℝ → ℝ := fun s => Real.exp (-(K * s)) * E s
  have hf : ∀ s, HasDerivAt f (Real.exp (-(K * s)) * (-K) * E s
      + Real.exp (-(K * s)) * ∑ i, 2 * a s i * (genMat q *ᵥ U s) i) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-(K * s))) (Real.exp (-(K * s)) * (-K)) s := by
      simpa using ((hasDerivAt_id s).const_mul K).neg.exp
    exact h1.mul (hE s)
  have hanti : Antitone f := antitone_of_hasDerivAt_nonpos hf fun s => by
    show _ ≤ (0:ℝ)
    have h1 := hEK s; have h2 := Real.exp_pos (-(K * s))
    have h3 := mul_le_mul_of_nonneg_left h1 h2.le
    nlinarith
  have hE0 : E 0 = 0 := Finset.sum_eq_zero fun i _ => by
    simp only [a]; rw [max_eq_right (by linarith [h0 i])]; ring
  have hft : f t ≤ 0 := by have := hanti ht; simpa [f, hE0] using this
  have hEt : E t ≤ 0 := by
    have := Real.exp_pos (-(K * t)); simp only [f] at hft; nlinarith
  have hai : a t i ^ 2 ≤ 0 := by
    have := Finset.single_le_sum (f := fun k => a t k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
    exact this.trans hEt
  have : a t i = 0 := by nlinarith [sq_nonneg (a t i)]
  have hle := le_max_left (U t i - M) 0
  simp only [a] at this; rw [this] at hle; linarith

/-- **Theorem 4.1(i), maximum principle.** For `q ≥ 0`, every solution of `U' = QU` satisfies
`min_l U_l(0) ≤ U_i(t) ≤ max_l U_l(0)` for `t ≥ 0`. -/
theorem markov_max_principle (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) {U : ℝ → ι → ℝ}
    (hU : ∀ t, HasDerivAt U (genMat q *ᵥ U t) t) {m M : ℝ} (h0 : ∀ i, U 0 i ∈ Set.Icc m M)
    {t : ℝ} (ht : 0 ≤ t) (i : ι) : U t i ∈ Set.Icc m M := by
  refine ⟨?_, markov_upper q hq hU (fun i => (h0 i).2) ht i⟩
  have hneg : ∀ t, HasDerivAt (fun s => -U s) (genMat q *ᵥ (-U t)) t := by
    intro t; rw [mulVec_neg]; exact (hU t).neg
  have := markov_upper q hq (U := fun s => -U s) hneg (M := -m)
    (fun i => by simp only [Pi.neg_apply]; linarith [(h0 i).1]) ht i
  simp only [Pi.neg_apply] at this; linarith

/-- **Theorem 4.1(ii), conservation.** If `πᵀQ = 0`, `∑_i π_i U_i(t)` is constant. -/
theorem stationary_conserved (q : ι → ι → ℝ) (π : ι → ℝ) (hπ : Stationary q π)
    {U : ℝ → ι → ℝ} (hU : ∀ t, HasDerivAt U (genMat q *ᵥ U t) t) (t : ℝ) :
    ∑ i, π i * U t i = ∑ i, π i * U 0 i := by
  have hd : ∀ s, HasDerivAt (fun s => ∑ i, π i * U s i) 0 s := by
    intro s
    have h := HasDerivAt.sum (u := univ) fun i _ => ((hasDerivAt_pi.1 (hU s)) i).const_mul (π i)
    convert h using 1
    · ext; simp
    · have := congrArg (fun v => v ⬝ᵥ U s) ((stationary_iff q π).1 hπ)
      simp only [zero_dotProduct, ← dotProduct_mulVec] at this
      simp only [dotProduct] at this
      rw [← this]
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa using this

/-- **Theorem 4.1(iii), energy identity `eq:energy`.**
`2 ∑_i π_i U_i (QU)_i = -∑_i ∑_j π_i q_{ij} (U_j - U_i)²` if `πᵀQ = 0`. -/
theorem markov_energy_identity (q : ι → ι → ℝ) (π : ι → ℝ) (hπ : Stationary q π) (U : ι → ℝ) :
    2 * wip π U (genMat q *ᵥ U) = -∑ i, ∑ j, π i * q i j * (U j - U i) ^ 2 := by
  have key : ∑ i, ∑ j, π i * q i j * (U j ^ 2 - U i ^ 2) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hπ j, Finset.mul_sum, Finset.sum_mul]
  have hl : 2 * wip π U (genMat q *ᵥ U)
      = ∑ i, ∑ j, 2 * (π i * U i * (q i j * (U j - U i))) := by
    simp only [wip, genMat_mulVec]
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have e : ∀ i j, π i * q i j * (U j - U i) ^ 2
      = π i * q i j * (U j ^ 2 - U i ^ 2) - 2 * (π i * U i * (q i j * (U j - U i))) :=
    fun i j => by ring
  rw [hl, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j]
  simp only [Finset.sum_sub_distrib, key]; ring

/-- **Theorem 4.1(iii), `p = 2`.** With `π ≥ 0` stationary, `‖U(t)‖_{π,2}` does not increase. -/
theorem markov_L2_contraction (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) (π : ι → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : Stationary q π) {U : ℝ → ι → ℝ}
    (hU : ∀ t, HasDerivAt U (genMat q *ᵥ U t) t) {t : ℝ} (ht : 0 ≤ t) :
    wip π (U t) (U t) ≤ wip π (U 0) (U 0) := by
  have h := energy_bound (W := diagonal π) (L := genMat q) (diagonal_transpose π) (ω := 0)
    (fun u => by
      have : u ⬝ᵥ (diagonal π *ᵥ (genMat q *ᵥ u)) = wip π u (genMat q *ᵥ u) := by
        simp only [dotProduct, mulVec_diagonal, wip]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      have := markov_energy_identity q π hπ u
      have : 0 ≤ ∑ i, ∑ j, π i * q i j * (u j - u i) ^ 2 := Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hπ0 i) (hq i j)) (sq_nonneg _)
      linarith) hU ht
  simpa [qf_diagonal] using h

/-- One forward Euler step `U⁺ = U + τQU`. -/
def eulerStep (q : ι → ι → ℝ) (τ : ℝ) (U : ι → ℝ) : ι → ℝ := fun i => U i + τ * ∑ j, q i j * (U j - U i)

theorem eulerStep_eq (q : ι → ι → ℝ) (τ : ℝ) (U : ι → ℝ) (i : ι) :
    eulerStep q τ U i = (1 - τ * ∑ j, q i j) * U i + ∑ j, τ * q i j * U j := by
  simp only [eulerStep, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_mul]
  ring_nf; simp only [Finset.mul_sum, Finset.sum_mul]; ring_nf

/-- **Theorem 4.1(iv), `p = ∞`.** Under `τ ∑_j q_{ij} ≤ 1`, a forward Euler step stays in
`[min U, max U]`. -/
theorem euler_step_max (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : ∀ i, τ * ∑ j, q i j ≤ 1) {U : ι → ℝ} {m M : ℝ} (hU : ∀ i, U i ∈ Set.Icc m M)
    (i : ι) : eulerStep q τ U i ∈ Set.Icc m M := by
  rw [eulerStep_eq]
  have h1 : 0 ≤ 1 - τ * ∑ j, q i j := by linarith [hcfl i]
  have hs : ∑ j, τ * q i j = τ * ∑ j, q i j := by rw [Finset.mul_sum]
  constructor
  · calc m = (1 - τ * ∑ j, q i j) * m + ∑ j, τ * q i j * m := by rw [← Finset.sum_mul, hs]; ring
      _ ≤ _ := by
        gcongr with j _
        · exact (hU i).1
        · exact mul_nonneg hτ (hq i j)
        · exact (hU j).1
  · calc _ ≤ (1 - τ * ∑ j, q i j) * M + ∑ j, τ * q i j * M := by
          gcongr with j _
          · exact (hU i).2
          · exact mul_nonneg hτ (hq i j)
          · exact (hU j).2
      _ = M := by rw [← Finset.sum_mul, hs]; ring

/-- **Theorem 4.1(iv), `1 ≤ p < ∞`.** Under `τ ∑_j q_{ij} ≤ 1`, with `π ≥ 0` stationary,
`∑ π_i |U⁺_i|^p ≤ ∑ π_i |U_i|^p` (Jensen for the stochastic matrix `I + τQ`). -/
theorem euler_step_contraction_p (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) (π : ι → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : Stationary q π) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : ∀ i, τ * ∑ j, q i j ≤ 1) {p : ℝ} (hp : 1 ≤ p) (U : ι → ℝ) :
    ∑ i, π i * |eulerStep q τ U i| ^ p ≤ ∑ i, π i * |U i| ^ p := by
  classical
  have hp0 : 0 ≤ p := by linarith
  -- pointwise Jensen
  have hpt : ∀ i, |eulerStep q τ U i| ^ p ≤
      (1 - τ * ∑ j, q i j) * |U i| ^ p + ∑ j, τ * q i j * |U j| ^ p := by
    intro i
    have h1 : 0 ≤ 1 - τ * ∑ j, q i j := by linarith [hcfl i]
    have htri : |eulerStep q τ U i| ≤ (1 - τ * ∑ j, q i j) * |U i| + ∑ j, τ * q i j * |U j| := by
      rw [eulerStep_eq]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg h1]
      gcongr
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hτ (hq i j))]
    -- convex combination on `Option ι`
    let wt : Option ι → ℝ := fun o => o.elim (1 - τ * ∑ j, q i j) fun j => τ * q i j
    let pt : Option ι → ℝ := fun o => o.elim (|U i|) fun j => |U j|
    have hw0 : ∀ o ∈ (univ : Finset (Option ι)), 0 ≤ wt o := fun o _ => by
      cases o with
      | none => exact h1
      | some j => exact mul_nonneg hτ (hq i j)
    have hw1 : ∑ o, wt o = 1 := by
      simp only [wt, Fintype.sum_option, Option.elim, ← Finset.mul_sum]; ring
    have hmem : ∀ o ∈ (univ : Finset (Option ι)), pt o ∈ Set.Ici (0 : ℝ) := fun o _ => by
      cases o <;> simp [pt]
    have hJ := (convexOn_rpow hp).map_sum_le hw0 hw1 hmem
    simp only [wt, pt, Fintype.sum_option, Option.elim, smul_eq_mul] at hJ
    calc |eulerStep q τ U i| ^ p ≤ ((1 - τ * ∑ j, q i j) * |U i| + ∑ j, τ * q i j * |U j|) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) htri hp0
      _ ≤ _ := hJ
  calc ∑ i, π i * |eulerStep q τ U i| ^ p
      ≤ ∑ i, π i * ((1 - τ * ∑ j, q i j) * |U i| ^ p + ∑ j, τ * q i j * |U j| ^ p) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hπ0 i)
    _ = ∑ i, π i * |U i| ^ p - τ * ∑ i, π i * (∑ j, q i j) * |U i| ^ p
          + τ * ∑ j, (∑ i, π i * q i j) * |U j| ^ p := by
        have e1 : ∑ i, π i * ∑ j, τ * q i j * |U j| ^ p
            = τ * ∑ j, (∑ i, π i * q i j) * |U j| ^ p := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        have e2 : ∑ i, π i * ((1 - τ * ∑ j, q i j) * |U i| ^ p)
            = ∑ i, π i * |U i| ^ p - τ * ∑ i, π i * (∑ j, q i j) * |U i| ^ p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        simp only [mul_add, Finset.sum_add_distrib]
        rw [e2, e1]
    _ = ∑ i, π i * |U i| ^ p := by
        have : ∑ j, (∑ i, π i * q i j) * |U j| ^ p = ∑ i, π i * (∑ j, q i j) * |U i| ^ p :=
          Finset.sum_congr rfl fun j _ => by rw [hπ j]
        rw [this]; ring

/-- **Theorem 4.1(iv), Runge–Kutta methods with `C > 0`**: every stage is a convex combination of
`Uⁿ` and forward Euler substeps (Lemma 6.1 of [A]), so the `π,p`-norm does not increase. -/
theorem rk_contraction_p (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) (π : ι → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : Stationary q π) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : ∀ i, τ * ∑ j, q i j ≤ 1) {p : ℝ} (hp : 1 ≤ p) (Y : ℕ → ι → ℝ) (v : ℕ → ℝ)
    (α : ℕ → ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (hα : ∀ k j, 0 ≤ α k j)
    (hsum : ∀ k, v k + ∑ j ∈ range k, α k j = 1)
    (hSO : ∀ k, 1 ≤ k → Y k = v k • Y 0 + ∑ j ∈ range k, α k j • eulerStep q τ (Y j)) (k : ℕ) :
    ∑ i, π i * |Y k i| ^ p ≤ ∑ i, π i * |Y 0 i| ^ p := by
  have hconv : ConvexOn ℝ Set.univ (fun U : ι → ℝ => ∑ i, π i * |U i| ^ p) := by
    refine ⟨convex_univ, fun U _ V _ a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc := (convexOn_rpow hp).2 (Set.mem_Ici.2 (abs_nonneg (U i)))
      (Set.mem_Ici.2 (abs_nonneg (V i))) ha hb hab
    simp only [smul_eq_mul] at hc
    have htri : |a * U i + b * V i| ≤ a * |U i| + b * |V i| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have := Real.rpow_le_rpow (abs_nonneg _) htri (by linarith : (0:ℝ) ≤ p)
    have := mul_le_mul_of_nonneg_left (this.trans hc) (hπ0 i)
    linarith
  exact ssp_convex_functional hconv Y (fun j => eulerStep q τ (Y j)) v α hv hα hsum hSO
    (fun _ => ⟨trivial, trivial⟩)
    (fun j => euler_step_contraction_p q hq π hπ0 hπ hτ hcfl hp (Y j)) k

/-- **Theorem 4.1(v).** With `c_ρ V_i ≤ π_i ≤ C_ρ V_i`, `‖U(t)‖²_V ≤ (C_ρ/c_ρ) ‖U(0)‖²_V`, i.e.
`‖e^{tQ}‖_V ≤ √ρ_h` with `ρ_h = max(π/V)/min(π/V)`. -/
theorem markov_volume_bound (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) (π V : ι → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : Stationary q π) {cρ Cρ : ℝ} (hc : 0 < cρ)
    (hlo : ∀ i, cρ * V i ≤ π i) (hhi : ∀ i, π i ≤ Cρ * V i) {U : ℝ → ι → ℝ}
    (hU : ∀ t, HasDerivAt U (genMat q *ᵥ U t) t) {t : ℝ} (ht : 0 ≤ t) :
    wip V (U t) (U t) ≤ (Cρ / cρ) * wip V (U 0) (U 0) := by
  have h1 : wip V (U t) (U t) ≤ cρ⁻¹ * wip π (U t) (U t) :=
    wip_le_of_le (fun i => by rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith [hlo i]) _
  have h2 := markov_L2_contraction q hq π hπ0 hπ hU ht
  have h3 : wip π (U 0) (U 0) ≤ Cρ * wip V (U 0) (U 0) := wip_le_of_le hhi _
  calc wip V (U t) (U t) ≤ cρ⁻¹ * wip π (U t) (U t) := h1
    _ ≤ cρ⁻¹ * (Cρ * wip V (U 0) (U 0)) := by gcongr; exact h2.trans h3
    _ = _ := by field_simp

/-! ### Proposition 4.3 and Proposition 4.5 -/

section Consistency

variable {D : ℕ} {J : Type*} [Fintype J]

/-- Dot product on `ℝ^D`. -/
def dot (x y : Fin D → ℝ) : ℝ := ∑ d, x d * y d

/-- **Proposition 4.3 (and 4.5(iii)), the algebraic identity.** At one particle with offsets
`x_j`, derivative weights `c_j` that reproduce linear functions (`∑_j c_{j,d} x_j = e_d`),
dissipation coefficients `γ^d_j` (`= |a_d||c_{j,d}|` for the scheme, corrected in Prop. 4.5),
and data `u_j - u_i = x_j·G + ρ_j` (Taylor):
`∑_j q_j(u_j-u_i) + a·G = ∑_d (∑_j γ^d_j x_j)·G + ∑_j q_j ρ_j` with `q_j = ∑_d (γ^d_j - a_d c_{j,d})`.
The first moment `∑_j γ^d_j x_j` is `|a_d| β^d` for the scheme. -/
theorem truncation_identity (x : J → Fin D → ℝ) (c γ : J → Fin D → ℝ) (a G : Fin D → ℝ)
    (hrep : ∀ d d', ∑ j, c j d * x j d' = if d = d' then 1 else 0)
    (du ρ : J → ℝ) (hdu : ∀ j, du j = dot (x j) G + ρ j) :
    ∑ j, (∑ d, (γ j d - a d * c j d)) * du j + dot a G
      = ∑ d, dot (fun d' => ∑ j, γ j d * x j d') G
        + ∑ j, (∑ d, (γ j d - a d * c j d)) * ρ j := by
  simp only [hdu, mul_add, Finset.sum_add_distrib, dot]
  have h1 : ∑ j, (∑ d, (γ j d - a d * c j d)) * ∑ d', x j d' * G d'
      = ∑ d, ∑ d', (∑ j, γ j d * x j d') * G d' - ∑ d, a d * ∑ d', (∑ j, c j d * x j d') * G d' := by
    simp only [Finset.sum_mul, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    congr 1 <;>
    · refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
      refine Finset.sum_comm.trans ?_
      exact Finset.sum_congr rfl fun d _ => Finset.sum_comm.trans
        (Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun j _ => by ring)
  have h2 : ∀ d, ∑ d', (∑ j, c j d * x j d') * G d' = G d := by
    intro d; simp only [hrep, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  rw [h1]; simp only [h2]; ring

/-- The remainder bound of Proposition 4.3: `|∑_j q_j ρ_j| ≤ (∑_j q_j) max|ρ|` for `q ≥ 0`. -/
theorem remainder_le (qj ρ : J → ℝ) (hq : ∀ j, 0 ≤ qj j) {R : ℝ} (hρ : ∀ j, |ρ j| ≤ R) :
    |∑ j, qj j * ρ j| ≤ (∑ j, qj j) * R := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => by
    rw [abs_mul, abs_of_nonneg (hq j)]; exact mul_le_mul_of_nonneg_left (hρ j) (hq j)

/-- **Proposition 4.3, centrally symmetric stencils.** If an involution `j ↦ j'` maps offsets to
their negatives and preserves `|c_j|` (Lemma 3.7(i) of [A]), the first moment
`β = ∑_j |c_j| x_j` vanishes. -/
theorem beta_zero_of_symmetric (x : J → Fin D → ℝ) (c : J → ℝ) (ρ : Equiv.Perm J)
    (hx : ∀ j, x (ρ j) = -x j) (hc : ∀ j, |c (ρ j)| = |c j|) :
    (fun d => ∑ j, |c j| * x j d) = 0 := by
  ext d
  have h := Equiv.sum_comp ρ (fun j => |c j| * x j d)
  simp only [hx, hc, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h
  simp only [Pi.zero_apply]; linarith

/-- **Proposition 4.5(iii).** If `∑_j ε^d_j x_j = -s_d β^d` with `β^d = ∑_j |c_{j,d}| x_j`, the
corrected coefficients `γ^d_j = s_d|c_{j,d}| + ε^d_j` have zero first moment; by
`truncation_identity` the truncation error is then `∑ q_j ρ_j = O(h)`. -/
theorem moment_corrected_first_moment (x : J → Fin D → ℝ) (c ε : J → Fin D → ℝ) (s : Fin D → ℝ)
    (hε : ∀ d d', ∑ j, ε j d * x j d' = -(s d * ∑ j, |c j d| * x j d')) (d : Fin D) :
    (fun d' => ∑ j, (s d * |c j d| + ε j d) * x j d') = 0 := by
  ext d'
  simp only [add_mul, Finset.sum_add_distrib, hε, Pi.zero_apply, Finset.mul_sum]
  simp only [mul_assoc, ← Finset.mul_sum]; ring

/-- **Proposition 4.5(i)** (positivity with corrected dissipation). Writing the update with
coefficients `γ ≥ s|c|` as `(1 - τ∑γ) U_i + τ ∑ γ (U_j - c F_d(U_j)/γ)`, each state
`U_j - (c/γ) F_d(U_j)` is admissible by Lemma 5.1 of [A] (hypothesis `LFHyp`), since
`γ/|c| ≥ s ≥ λ_d(U_j)`. -/
theorem moment_corrected_admissible {E : Type*} [AddCommGroup E] [Module ℝ E] {G : Set E}
    (hG : Convex ℝ G) {F : Fin D → E → E} {lam : Fin D → E → ℝ} (hLF : LFHyp G F lam)
    (c s γ : J → Fin D → ℝ) (Ui : E) (Uj : J → E) (ha : ∀ d, ∑ j, c j d = 0)
    (hs : ∀ j d, lam d (Uj j) ≤ s j d) (hspos : ∀ j d, 0 < s j d)
    (hγ : ∀ j d, s j d * |c j d| ≤ γ j d) (hUi : Ui ∈ G) (hUj : ∀ j, Uj j ∈ G)
    {τ : ℝ} (hτ : 0 ≤ τ) (hcfl : τ * ∑ j, ∑ d, γ j d ≤ 1) :
    Ui + τ • ∑ j, ∑ d, (γ j d • (Uj j - Ui) - c j d • (F d (Uj j) - F d Ui)) ∈ G := by
  classical
  have hγ0 : ∀ j d, 0 ≤ γ j d := fun j d =>
    le_trans (mul_nonneg (hspos j d).le (abs_nonneg _)) (hγ j d)
  let W : J × Fin D → E := fun p =>
    if c p.1 p.2 = 0 then Uj p.1 else Uj p.1 - (c p.1 p.2 / γ p.1 p.2) • F p.2 (Uj p.1)
  have hW : ∀ p, W p ∈ G := by
    intro ⟨j, d⟩
    simp only [W]
    split_ifs with h
    · exact hUj j
    · have hc : 0 < |c j d| := abs_pos.2 h
      have hγp : 0 < γ j d := lt_of_lt_of_le (mul_pos (hspos j d) hc) (hγ j d)
      set s' := γ j d / |c j d|
      have hs' : s j d ≤ s' := by rw [le_div_iff₀ hc]; exact hγ j d
      have hσ : Real.sign (c j d) = 1 ∨ Real.sign (c j d) = -1 := by
        rcases lt_or_gt_of_ne h with h' | h'
        · right; exact Real.sign_of_neg h'
        · left; exact Real.sign_of_pos h'
      have := hLF _ (hUj j) d (Real.sign (c j d)) s' hσ ((hs j d).trans hs')
        (div_pos hγp hc)
      convert this using 3
      simp only [s']
      rw [← ConsData.sign_mul_self (c j d)]
      field_simp
      rcases hσ with h1 | h1 <;> rw [h1] <;> ring
  let β : J × Fin D → ℝ := fun p => τ * γ p.1 p.2
  have hupd : Ui + τ • ∑ j, ∑ d, (γ j d • (Uj j - Ui) - c j d • (F d (Uj j) - F d Ui))
      = (1 - ∑ p, β p) • Ui + ∑ p, β p • W p := by
    have hzero : ∑ j, ∑ d, c j d • F d Ui = 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun d _ => by rw [← Finset.sum_smul, ha d, zero_smul]
    have hterm : ∀ j d, γ j d • W (j, d) = γ j d • Uj j - c j d • F d (Uj j) := by
      intro j d
      simp only [W]
      split_ifs with h
      · simp [h]
      · have hγp : 0 < γ j d := lt_of_lt_of_le (mul_pos (hspos j d) (abs_pos.2 h)) (hγ j d)
        rw [smul_sub, smul_smul, mul_div_cancel₀ _ hγp.ne']
    simp only [β, Fintype.sum_prod_type, ← smul_smul, ← Finset.smul_sum, hterm]
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, sub_smul, one_smul, hzero,
      Finset.sum_smul, smul_zero, sub_zero]
    simp only [← Finset.smul_sum]
    have e : τ • ∑ j, ∑ d, γ j d • Ui = ∑ j, ∑ d, (τ * γ j d) • Ui := by
      simp only [Finset.smul_sum, smul_smul]
    rw [e]; abel
  rw [hupd]
  have hβ : ∀ p, 0 ≤ β p := fun p => mul_nonneg hτ (hγ0 _ _)
  have hsum : ∑ p, β p = τ * ∑ j, ∑ d, γ j d := by
    simp only [β, ← Finset.mul_sum, Fintype.sum_prod_type]
  let wt : Option (J × Fin D) → ℝ := fun o => o.elim (1 - ∑ p, β p) β
  let pt : Option (J × Fin D) → E := fun o => o.elim Ui W
  have hmem := hG.sum_mem (t := univ) (w := wt) (z := pt)
    (fun o _ => by
      cases o with
      | none => simp only [wt, Option.elim]; linarith [hsum]
      | some p => exact hβ p)
    (by simp [wt, Fintype.sum_option])
    (fun o _ => by
      cases o with
      | none => exact hUi
      | some p => exact hW p)
  simpa [wt, pt, Fintype.sum_option] using hmem

end Consistency

/-! ### Theorem 4.4 -/

/-- **The corrector identity of Theorem 4.4.** For a generator `q` and vector-valued `δ_i` and
`g_i` (`g_i = ∇u(x_i)`):
`(Q(δ·g))_i = (Qδ)_i·g_i + ∑_j q_{ij} δ_j·(g_j - g_i)`. -/
theorem corrector_identity {D : ℕ} (q : ι → ι → ℝ) (δ g : ι → Fin D → ℝ) (i : ι) :
    (genMat q *ᵥ fun k => ∑ d, δ k d * g k d) i
      = ∑ d, (∑ j, q i j * (δ j d - δ i d)) * g i d
        + ∑ j, q i j * ∑ d, δ j d * (g j d - g i d) := by
  simp only [genMat_mulVec]
  have e : ∀ j, q i j * ((∑ d, δ j d * g j d) - ∑ d, δ i d * g i d)
      = ∑ d, q i j * (δ j d - δ i d) * g i d + q i j * ∑ d, δ j d * (g j d - g i d) := by
    intro j
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => by rw [Finset.sum_mul]

/-- **Theorem 4.4 (drift), the error estimate.** Let `π > 0` be stationary for the generator
`q`, `U' = QU`, and let `u(t)` (the exact solution of the effective equation sampled at the
particles) satisfy `u' = Qu - τ_tr` where the truncation error splits as `τ_tr = Qψ + r'`
with a corrector `ψ` (`ψ_i = ∑_d |a_d| δ^d_i·∇u(x_i)`, `corrector_identity`), and
`‖r'(t)‖_π ≤ ε`, `‖ψ'(t)‖_π ≤ ε'`, `‖ψ(t)‖_π ≤ P`. Then
`‖U(t) - u(t)‖_π ≤ ‖U(0) - u(0)‖_π + 2P + (ε + ε') t`.
With `ε = C(h + η_h)`, `ε' = Cη_h`, `P = Cη_h` this is `eq:drifterror`. -/
theorem drift_error_bound (q : ι → ι → ℝ) (hq : ∀ i j, 0 ≤ q i j) (π : ι → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : Stationary q π) {U u ψ ψ' r' τtr : ℝ → ι → ℝ}
    (hU : ∀ t, HasDerivAt U (genMat q *ᵥ U t) t)
    (hu : ∀ t, HasDerivAt u (genMat q *ᵥ u t - τtr t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hsplit : ∀ t, τtr t = genMat q *ᵥ ψ t + r' t) {ε ε' P : ℝ}
    (hr : ∀ t, 0 ≤ t → Real.sqrt (wip π (r' t) (r' t)) ≤ ε)
    (hψ'b : ∀ t, 0 ≤ t → Real.sqrt (wip π (ψ' t) (ψ' t)) ≤ ε')
    (hψb : ∀ t, 0 ≤ t → Real.sqrt (wip π (ψ t) (ψ t)) ≤ P) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (wip π (U t - u t) (U t - u t)) ≤
      Real.sqrt (wip π (U 0 - u 0) (U 0 - u 0)) + 2 * P + (ε + ε') * t := by
  -- the modified error `ẽ = (U - u) + ψ` solves `ẽ' = Qẽ + (r' + ψ')`
  set e : ℝ → ι → ℝ := fun s => U s - u s + ψ s
  have he : ∀ s, HasDerivAt e (genMat q *ᵥ e s + (r' s + ψ' s)) s := by
    intro s
    have := ((hU s).sub (hu s)).add (hψ s)
    convert this using 1
    simp only [e, mulVec_add, mulVec_sub, hsplit s]; abel
  have hdiss : ∀ v, wip π v (genMat q *ᵥ v) ≤ 0 := by
    intro v
    have := markov_energy_identity q π hπ v
    have : 0 ≤ ∑ i, ∑ j, π i * q i j * (v j - v i) ^ 2 := Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hπ0 i) (hq i j)) (sq_nonneg _)
    linarith
  -- triangle inequality for the weighted norm
  have tri : ∀ v w : ι → ℝ, Real.sqrt (wip π (v + w) (v + w)) ≤
      Real.sqrt (wip π v v) + Real.sqrt (wip π w w) := by
    intro v w
    rw [Real.sqrt_le_left (by positivity)]
    have hcs := wip_le_sqrt_mul_sqrt hπ0 v w
    have e1 : wip π (v + w) (v + w) = wip π v v + 2 * wip π v w + wip π w w := by
      simp only [wip, Pi.add_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, add_sq, Real.sq_sqrt (wip_self_nonneg hπ0 v), Real.sq_sqrt (wip_self_nonneg hπ0 w)]
    linarith
  have hforce : ∀ s, 0 ≤ s → Real.sqrt (wip π (r' s + ψ' s) (r' s + ψ' s)) ≤ ε + ε' :=
    fun s hs => (tri _ _).trans (add_le_add (hr s hs) (hψ'b s hs))
  have hmain := energy_forced hπ0 hdiss he hforce ht
  have hneg : ∀ s, Real.sqrt (wip π (-ψ s) (-ψ s)) = Real.sqrt (wip π (ψ s) (ψ s)) := by
    intro s; congr 1; simp [wip]
  calc Real.sqrt (wip π (U t - u t) (U t - u t))
      = Real.sqrt (wip π (e t + -ψ t) (e t + -ψ t)) := by simp [e]
    _ ≤ Real.sqrt (wip π (e t) (e t)) + Real.sqrt (wip π (ψ t) (ψ t)) :=
        (tri _ _).trans (by rw [hneg])
    _ ≤ Real.sqrt (wip π (e 0) (e 0)) + (ε + ε') * t + P := by
        linarith [hψb t ht]
    _ ≤ Real.sqrt (wip π (U 0 - u 0) (U 0 - u 0)) + P + (ε + ε') * t + P := by
        have := tri (U 0 - u 0) (ψ 0)
        linarith [hψb 0 le_rfl]
    _ = _ := by ring

end Meshfree.Stability
