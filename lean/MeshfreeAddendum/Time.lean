import MeshfreeAddendum.Positivity

/-!
# Time integration and stage-wise MOOD (Section 6 of the addendum)

* **Lemma 6.1** (canonical Shu–Osher form): `soAlpha_strictLower`, `soV_add_sum`,
  `shuOsher_form`.
* Canonical forms of forward Euler, Heun (RK2) and SSPRK3 at `r = 1`: `rk1_canonical`,
  `rk2_canonical`, `rk3_canonical` (exact rational arithmetic).
* **Remark 6.2** (SSPRK(5,4)): `ssprk54_elimination` (exact algebra) and
  `ssprk54_negative_coefficient` (negativity for all coefficients within the rounding
  of Table 1; the coefficients themselves are not derived in Lean).
* **Algorithm 1** (MOOD checkpoint): `Checkpoint.run`, termination by construction,
  `Checkpoint.run_spec` (invariant), `Checkpoint.run_admissible`.
* **Theorem 6.3**: `stagewise_mood_admissible`.
* **Corollary 6.4**: `ssp_order_one`.
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree

/-! ### Lemma 6.1 -/

section ShuOsher

variable {n : ℕ}

/-- Strictly lower triangular: `A k j = 0` for `k ≤ j`. -/
def StrictLower (A : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ k j, k ≤ j → A k j = 0

/-- `α^{(r)} = r Â (Id + r Â)⁻¹`, eq. `eq:canonical`. -/
noncomputable def soAlpha (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (r • A) * (1 + r • A)⁻¹

/-- `v^{(r)} = (Id - α^{(r)}) e`, eq. `eq:canonical`. -/
noncomputable def soV (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  (1 - soAlpha r A) *ᵥ (fun _ => 1)

theorem soV_add_sum (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    soV r A k + ∑ j, soAlpha r A k j = 1 := by
  simp [soV, mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib]

theorem one_add_lower {A : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) (r : ℝ) :
    (1 + r • A).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp [Matrix.one_apply, hij'.ne, hA i j hij'.le]

theorem det_one_add {A : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) (r : ℝ) :
    (1 + r • A).det = 1 := by
  rw [det_of_isLowerTriangular _ (one_add_lower hA r)]
  exact Finset.prod_eq_one fun i _ => by simp [hA i i le_rfl]

theorem isUnit_one_add {A : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) (r : ℝ) :
    IsUnit (1 + r • A).det := by rw [det_one_add hA]; exact isUnit_one

/-- **Lemma 6.1**, triangularity: `α^{(r)}` is strictly lower triangular. -/
theorem soAlpha_strictLower {A : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) (r : ℝ) :
    StrictLower (soAlpha r A) := by
  let _ := invertibleOfIsUnitDet _ (isUnit_one_add hA r)
  have hinv : ((1 + r • A)⁻¹).IsLowerTriangular :=
    blockTriangular_inv_of_blockTriangular (one_add_lower hA r)
  intro k j hkj
  simp only [soAlpha, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hlk : k ≤ l
  · simp [hA k l hlk]
  · have hjl : l < j := lt_of_lt_of_le (not_le.1 hlk) hkj
    rw [hinv (show OrderDual.toDual j < OrderDual.toDual l from hjl), mul_zero]

/-- `(Id + rÂ)⁻¹ = Id - α^{(r)}`. -/
theorem inv_one_add_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) (r : ℝ) :
    (1 + r • A)⁻¹ = 1 - soAlpha r A := by
  have hu := isUnit_one_add hA r
  have : (1 - soAlpha r A) = ((1 + r • A) - r • A) * (1 + r • A)⁻¹ := by
    rw [Matrix.sub_mul, mul_nonsing_inv _ hu, soAlpha]
  rw [this, add_sub_cancel_right, Matrix.one_mul]

/-- Action of a real matrix on a vector of states. -/
def act {E : Type*} [AddCommGroup E] [Module ℝ E] (M : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → E) : Fin n → E := fun k => ∑ j, M k j • X j

section act
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem act_mul (M N : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → E) :
    act (M * N) X = act M (act N X) := by
  funext k
  simp only [act, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem act_one (X : Fin n → E) : act 1 X = X := by
  funext k
  simp [act, Matrix.one_apply]

theorem act_add_left (M N : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → E) :
    act (M + N) X = act M X + act N X := by
  funext k; simp [act, add_smul, Finset.sum_add_distrib]

theorem act_smul_left (r : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → E) :
    act (r • M) X = r • act M X := by
  funext k; simp [act, Finset.smul_sum, smul_smul]

theorem act_add_right (M : Matrix (Fin n) (Fin n) ℝ) (X Y : Fin n → E) :
    act M (X + Y) = act M X + act M Y := by
  funext k; simp [act, smul_add, Finset.sum_add_distrib]

theorem act_smul_right (r : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → E) :
    act M (r • X) = r • act M X := by
  funext k; simp [act, Finset.smul_sum, smul_comm r]

theorem act_const (M : Matrix (Fin n) (Fin n) ℝ) (U : E) (k : Fin n) :
    act M (fun _ => U) k = (∑ j, M k j) • U := by
  simp [act, Finset.sum_smul]

end act

/-- **Lemma 6.1** (canonical Shu–Osher form). If the stages satisfy the Butcher form
`Y = e Uⁿ + Δt Â L` (rows `k ≤ s` and the update as the last row), then for every
`r ≠ 0` (the addendum uses `r > 0`):
`Y_k = v_k Uⁿ + ∑_j α_{kj} (Y_j + (Δt/r) L_j)`. -/
theorem shuOsher_form {E : Type*} [AddCommGroup E] [Module ℝ E]
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) {r : ℝ} (hr : r ≠ 0) (Δt : ℝ)
    (U : E) (Y L : Fin n → E) (hRK : Y = (fun _ => U) + Δt • act A L) (k : Fin n) :
    Y k = soV r A k • U + ∑ j, soAlpha r A k j • (Y j + (Δt / r) • L j) := by
  set B := 1 + r • A
  set W := Y + (Δt / r) • L
  have hBY : act B Y = (fun _ => U) + act (r • A) W := by
    simp only [B, act_add_left, act_one, act_smul_left, W, act_add_right, act_smul_right]
    nth_rewrite 1 [hRK]
    rw [smul_smul, div_mul_cancel₀ _ hr]
    abel
  have hcomm : (1 + r • A)⁻¹ * (r • A) = soAlpha r A := by
    have hu := isUnit_one_add hA r
    have h1 : (r • A) * (1 + r • A) = (1 + r • A) * (r • A) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    calc (1 + r • A)⁻¹ * (r • A) = (1 + r • A)⁻¹ * (r • A) * ((1 + r • A) * (1 + r • A)⁻¹) := by
          rw [mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (1 + r • A)⁻¹ * ((r • A) * (1 + r • A)) * (1 + r • A)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (1 + r • A)⁻¹ * ((1 + r • A) * (r • A)) * (1 + r • A)⁻¹ := by rw [h1]
      _ = soAlpha r A := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, soAlpha]
  have hY : Y = act B⁻¹ (fun _ => U) + act (soAlpha r A) W := by
    have hu := isUnit_one_add hA r
    calc Y = act (B⁻¹ * B) Y := by rw [nonsing_inv_mul _ hu, act_one]
      _ = act B⁻¹ (act B Y) := act_mul _ _ _
      _ = _ := by rw [hBY, act_add_right, ← act_mul, hcomm]
  conv_lhs => rw [hY]
  have hv : (∑ j, B⁻¹ k j) = soV r A k := by
    simp only [B, inv_one_add_eq hA, soV, mulVec, dotProduct, mul_one]
  simp only [Pi.add_apply, act_const, hv]
  rfl

/-! #### Canonical forms of FE, RK2 and RK3 at `r = 1` -/

/-- If `α (Id + rÂ) = rÂ` then `α = α^{(r)}`. -/
theorem soAlpha_eq_of {A α : Matrix (Fin n) (Fin n) ℝ} (hA : StrictLower A) (r : ℝ)
    (h : α * (1 + r • A) = r • A) : soAlpha r A = α := by
  rw [soAlpha]
  nth_rewrite 1 [← h]
  rw [Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_one_add hA r), Matrix.mul_one]

/-- Butcher matrix `Â` of SSPRK3 (Shu–Osher), with the weights as last row. -/
noncomputable def rk3A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 1/4, 1/4, 0, 0; 1/6, 1/6, 2/3, 0]

noncomputable def rk3Alpha : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 1/4, 0, 0; 0, 0, 2/3, 0]

theorem rk3A_strictLower : StrictLower rk3A := by
  intro k j h
  fin_cases k <;> fin_cases j <;> simp_all [rk3A] <;> omega

/-- SSPRK3 at `r = 1`: `Y₂ = W₁`, `Y₃ = ¾Uⁿ + ¼W₂`, `Uⁿ⁺¹ = ⅓Uⁿ + ⅔W₃`, all
coefficients non-negative. -/
theorem rk3_canonical : soAlpha 1 rk3A = rk3Alpha ∧ soV 1 rk3A = ![1, 0, 3/4, 1/3] ∧
    (∀ k j, 0 ≤ soAlpha 1 rk3A k j) ∧ (∀ k, 0 ≤ soV 1 rk3A k) := by
  have hα : soAlpha 1 rk3A = rk3Alpha := by
    apply soAlpha_eq_of rk3A_strictLower
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rk3A, rk3Alpha, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> norm_num
  have hv : soV 1 rk3A = ![1, 0, 3/4, 1/3] := by
    rw [soV, hα]
    funext k
    fin_cases k <;> simp [rk3Alpha, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply] <;>
      norm_num
  refine ⟨hα, hv, fun k j => ?_, fun k => ?_⟩
  · rw [hα]; fin_cases k <;> fin_cases j <;> simp [rk3Alpha] <;> norm_num
  · rw [hv]; fin_cases k <;> simp <;> norm_num

noncomputable def rk2A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 1, 0, 0; 1/2, 1/2, 0]

/-- Heun (SSPRK2) at `r = 1`: `Y₂ = W₁`, `Uⁿ⁺¹ = ½Uⁿ + ½W₂`. -/
theorem rk2_canonical : soAlpha 1 rk2A = !![0, 0, 0; 1, 0, 0; 0, 1/2, 0] ∧
    soV 1 rk2A = ![1, 0, 1/2] := by
  have hA : StrictLower rk2A := by
    intro k j h; fin_cases k <;> fin_cases j <;> simp_all [rk2A] <;> omega
  have hα : soAlpha 1 rk2A = !![0, 0, 0; 1, 0, 0; 0, 1/2, 0] := by
    apply soAlpha_eq_of hA
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rk2A, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> norm_num
  refine ⟨hα, ?_⟩
  rw [soV, hα]
  funext k
  fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply] <;> norm_num

/-- Forward Euler at `r = 1`: `Uⁿ⁺¹ = W₁`. -/
theorem rk1_canonical : soAlpha 1 (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 0; 1, 0] ∧
    soV 1 (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = ![1, 0] := by
  have hA : StrictLower (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro k j h; fin_cases k <;> fin_cases j <;> simp_all <;> omega
  have hα : soAlpha 1 (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 0; 1, 0] := by
    apply soAlpha_eq_of hA
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.one_apply]
  refine ⟨hα, ?_⟩
  rw [soV, hα]
  funext k
  fin_cases k <;> simp [mulVec, dotProduct, Matrix.one_apply]

end ShuOsher

/-! ### Remark 6.2: SSPRK(5,4) -/

section SSPRK54

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Exact elimination of `W₂` and `W₄` from the canonical form of SSPRK(5,4). -/
theorem ssprk54_elimination (v3 v5 v6 a32 a54 a62 a64 a65 : ℝ) (h32 : a32 ≠ 0) (h54 : a54 ≠ 0)
    (U W2 W4 W5 Y3 Y5 U1 : E) (hY3 : Y3 = v3 • U + a32 • W2) (hY5 : Y5 = v5 • U + a54 • W4)
    (hU1 : U1 = v6 • U + a62 • W2 + a64 • W4 + a65 • W5) :
    U1 = (a62 / a32) • Y3 + (a64 / a54) • Y5 + a65 • W5
      + (v6 - a62 * v3 / a32 - a64 * v5 / a54) • U := by
  rw [hU1, hY3, hY5]
  simp only [smul_add, smul_smul, add_smul, sub_smul]
  rw [div_mul_cancel₀ _ h32, div_mul_cancel₀ _ h54]
  have e1 : a62 / a32 * v3 = a62 * v3 / a32 := by ring
  have e2 : a64 / a54 * v5 = a64 * v5 / a54 := by ring
  rw [e1, e2]
  abel

/-- The coefficient of `Uⁿ` after the elimination is negative for every choice of the
canonical coefficients within `±5·10⁻⁵` of the rounded values of Table 1
(`v₃ = 0.4444`, `v₅ = 0.1781`, `v₆ = 0.2380`, `α₃₂ = 0.5556`, `α₅₄ = 0.8219`,
`α₆₂ = 0.2874`, `α₆₄ = 0.1337`). The table values themselves come from a floating-point
computation and are an assumption here. -/
theorem ssprk54_negative_coefficient (v3 v5 v6 a32 a54 a62 a64 : ℝ)
    (hv3 : |v3 - 0.4444| ≤ 0.00005) (hv5 : |v5 - 0.1781| ≤ 0.00005)
    (hv6 : |v6 - 0.2380| ≤ 0.00005) (ha32 : |a32 - 0.5556| ≤ 0.00005)
    (ha54 : |a54 - 0.8219| ≤ 0.00005) (ha62 : |a62 - 0.2874| ≤ 0.00005)
    (ha64 : |a64 - 0.1337| ≤ 0.00005) :
    v6 - a62 * v3 / a32 - a64 * v5 / a54 < 0 := by
  rw [abs_le] at hv3 hv5 hv6 ha32 ha54 ha62 ha64
  have h32 : 0 < a32 := by linarith
  have h54 : 0 < a54 := by linarith
  have t1 : 0.2287 ≤ a62 * v3 / a32 := by
    rw [le_div_iff₀ h32]
    nlinarith [mul_le_mul (by linarith : (0.28735 : ℝ) ≤ a62) (by linarith : (0.44435 : ℝ) ≤ v3)
      (by norm_num) (by linarith)]
  have t2 : 0.0289 ≤ a64 * v5 / a54 := by
    rw [le_div_iff₀ h54]
    nlinarith [mul_le_mul (by linarith : (0.13365 : ℝ) ≤ a64) (by linarith : (0.17805 : ℝ) ≤ v5)
      (by norm_num) (by linarith)]
  linarith

end SSPRK54

/-! ### Algorithm 1: the MOOD checkpoint -/

section MOOD

variable {I : Type*} [DecidableEq I] {E : Type*}

/-- One MOOD checkpoint `k` (Algorithm 1) for fixed `Uⁿ`, stages `Y₁,…,Y_{k-1}` and
operators `K₁,…,K_{k-2}`.
* `W ord i` is the substep `W_{k-1,i} = Y_{k-1,i} + (Δt/C) L_i(Y_{k-1})` computed with
  the orders `ord`;
* `bad i Z` says that the state `Z` of particle `i` is flagged (PAD or DMP with respect
  to `Y_{k-1}`);
* `hood C` is the set of particles within `ϱ` hops of `C`. -/
structure Checkpoint (I E : Type*) where
  W : (I → ℕ) → I → E
  bad : I → E → Prop
  hood : Finset I → Finset I

namespace Checkpoint

variable (X : Checkpoint I E)

/-- Lower the orders on `C` by one. -/
def lowerOn (k : I → ℕ) (C : Finset I) : I → ℕ := fun i => if i ∈ C then k i - 1 else k i

open Classical in
/-- The particles of `T` that are flagged and can still be lowered. -/
noncomputable def toLower (k : I → ℕ) (T : Finset I) : Finset I :=
  T.filter (fun i => X.bad i (X.W k i) ∧ 1 < k i)

theorem sum_lowerOn_lt [Fintype I] (k : I → ℕ) (T : Finset I) (h : X.toLower k T ≠ ∅) :
    ∑ i, lowerOn k (X.toLower k T) i < ∑ i, k i := by
  classical
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
  apply Finset.sum_lt_sum
  · intro j _; simp only [lowerOn]; split_ifs <;> omega
  · refine ⟨i, mem_univ i, ?_⟩
    have : 1 < k i := by
      simp only [toLower, mem_filter] at hi; exact hi.2.2
    simp only [lowerOn, hi, ite_true]; omega

/-- The loop of Algorithm 1: returns the final orders. Termination: every pass that does
not break lowers at least one order, and the sum of the orders decreases. -/
noncomputable def run [Fintype I] (k : I → ℕ) (T : Finset I) : I → ℕ :=
  if h : X.toLower k T = ∅ then k else run (lowerOn k (X.toLower k T)) (X.hood (X.toLower k T))
termination_by ∑ i, k i
decreasing_by exact X.sum_lowerOn_lt k T h

/-- Exact locality (Section 6.2): lowering orders on `C` does not change the substeps
outside `hood C`. -/
def Local : Prop :=
  ∀ (k : I → ℕ) (C : Finset I), ∀ i ∉ X.hood C, X.W (lowerOn k C) i = X.W k i

/-- Invariant of the loop: particles outside `T` are unflagged or at order one. -/
def Inv (k : I → ℕ) (T : Finset I) : Prop := ∀ i ∉ T, X.bad i (X.W k i) → k i = 1

theorem run_spec [Fintype I] (hhood : ∀ C, C ⊆ X.hood C) (hloc : X.Local) :
    ∀ (n : ℕ) (k : I → ℕ) (T : Finset I), ∑ i, k i = n → (∀ i, 1 ≤ k i) → X.Inv k T →
      (∀ i, 1 ≤ X.run k T i) ∧ ∀ i, X.bad i (X.W (X.run k T) i) → X.run k T i = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k T hn hk hinv
  rw [run]
  split_ifs with h
  · refine ⟨hk, fun i hi => ?_⟩
    by_cases hiT : i ∈ T
    · have : i ∉ X.toLower k T := by rw [h]; exact Finset.notMem_empty i
      classical
      simp only [toLower, mem_filter, not_and, not_lt] at this
      have := this hiT hi; have := hk i; omega
    · exact hinv i hiT hi
  · set C := X.toLower k T
    have hlt := X.sum_lowerOn_lt k T h
    refine ih _ (hn ▸ hlt) _ _ rfl ?_ ?_
    · intro i; simp only [lowerOn]
      split_ifs with hiC
      · classical
        simp only [C, toLower, mem_filter] at hiC; omega
      · exact hk i
    · intro i hi hbad
      have hiC : i ∉ C := fun h' => hi (hhood C h')
      rw [hloc k C i hi] at hbad
      simp only [lowerOn, hiC, ite_false]
      by_cases hiT : i ∈ T
      · classical
        simp only [C, toLower, mem_filter, not_and, not_lt] at hiC
        have := hiC hiT hbad; have := hk i; omega
      · exact hinv i hiT hbad

/-- **Algorithm 1 + Proposition 5.7**: if PAD flags every inadmissible substep and every
particle at order one has an admissible substep (Proposition 5.7 with (H1)–(H4)), the
checkpoint terminates with admissible substeps at all interior particles, for any
initial orders `≥ 1`. -/
theorem run_admissible [Fintype I] {G : Set E} (hhood : ∀ C, C ⊆ X.hood C) (hloc : X.Local)
    (hPAD : ∀ i Z, Z ∉ G → X.bad i Z)
    (hone : ∀ (k : I → ℕ) i, (∀ l, 1 ≤ k l) → k i = 1 → X.W k i ∈ G)
    (k₀ : I → ℕ) (hk₀ : ∀ i, 1 ≤ k₀ i) :
    ∀ i, X.W (X.run k₀ univ) i ∈ G := by
  obtain ⟨hk, hspec⟩ := X.run_spec hhood hloc _ k₀ univ rfl hk₀
    (fun i hi => absurd (mem_univ i) hi)
  intro i
  by_contra hW
  exact hW (hone _ i hk (hspec i (hPAD i _ hW)))

end Checkpoint

end MOOD

/-! ### Theorem 6.3 and Corollary 6.4 -/

section Stages

variable {P : Type*} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The SSP induction over the stages. Stages `Y 0 = Uⁿ, Y 1, …, Y s = Uⁿ⁺¹` at all
particles, substeps `W j` (`j < s`) at the interior particles; Shu–Osher form with
non-negative coefficients summing to one (Lemma 6.1 at `r = C > 0`); the boundary
operator preserves admissibility (H3); and each substep is admissible as soon as its
stage is (the checkpoint result). Then all stages and substeps are admissible. -/
theorem ssp_stages {G : Set E} (hG : Convex ℝ G) (s : ℕ) (interior : P → Prop)
    (Y : ℕ → P → E) (W : ℕ → P → E) (v : ℕ → ℝ) (α : ℕ → ℕ → ℝ)
    (hv : ∀ k, 0 ≤ v k) (hα : ∀ k j, 0 ≤ α k j)
    (hsum : ∀ k, v k + ∑ j ∈ range k, α k j = 1)
    (hSO : ∀ k, 1 ≤ k → k ≤ s → ∀ i, interior i →
      Y k i = v k • Y 0 i + ∑ j ∈ range k, α k j • W j i)
    (hY0 : ∀ p, Y 0 p ∈ G)
    (hghost : ∀ k, (∀ i, interior i → Y k i ∈ G) → ∀ p, Y k p ∈ G)
    (hW : ∀ j < s, (∀ p, Y j p ∈ G) → ∀ i, interior i → W j i ∈ G) :
    ∀ k ≤ s, (∀ p, Y k p ∈ G) ∧ ∀ j < k, ∀ i, interior i → W j i ∈ G := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hks
  -- substeps of all earlier checkpoints are admissible
  have hWprev : ∀ j < k, ∀ i, interior i → W j i ∈ G := by
    intro j hj
    exact hW j (by omega) (ih j hj (by omega)).1
  refine ⟨?_, hWprev⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; exact hY0
  apply hghost
  intro i hi
  rw [hSO k hpos hks i hi]
  -- a convex combination of `Uⁿ` and the substeps
  classical
  let wt : Option ℕ → ℝ := fun o => o.elim (v k) (fun j => α k j)
  let pt : Option ℕ → E := fun o => o.elim (Y 0 i) (fun j => W j i)
  let t : Finset (Option ℕ) := insert none ((range k).map Function.Embedding.some)
  have hmem := hG.sum_mem (t := t) (w := wt) (z := pt)
    (fun o _ => by cases o <;> simp [wt, hv, hα])
    (by simp [t, wt, Finset.sum_insert, hsum])
    (fun o ho => by
      cases o with
      | none => exact hY0 i
      | some j =>
        have hj : j < k := by simpa [t] using ho
        exact hWprev j hj i hi)
  simpa [t, wt, pt, Finset.sum_insert] using hmem

/-- **Theorem 6.3 (admissibility of stage-wise MOOD).** For every checkpoint `j < s` let
`X j` be the checkpoint of Algorithm 1 built from the stage `Y j`, with PAD flagging
inadmissible states, exact locality and `hood C ⊇ C`, and assume that every particle at
order one has an admissible substep whenever `Y j` is admissible at all particles — this
is Proposition 5.7 under (H1), (H2) and (H4), see `local_admissibility_order_one`. Let the
stages satisfy the canonical Shu–Osher form with the substeps produced by the
checkpoints (Lemma 6.1, `shuOsher_form`), with `α, v ≥ 0` (`C > 0`), and let (H3) hold.
Then every checkpoint ends with admissible substeps and all stages, including `Uⁿ⁺¹`, are
admissible, for any initial orders. -/
theorem stagewise_mood_admissible {I : Type*} [Fintype I] [DecidableEq I]
    {G : Set E} (hG : Convex ℝ G) (s : ℕ) (Y : ℕ → I ⊕ P → E)
    (X : ℕ → Checkpoint I E) (k₀ : ℕ → I → ℕ) (hk₀ : ∀ j i, 1 ≤ k₀ j i)
    (v : ℕ → ℝ) (α : ℕ → ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (hα : ∀ k j, 0 ≤ α k j)
    (hsum : ∀ k, v k + ∑ j ∈ range k, α k j = 1)
    (hhood : ∀ j C, C ⊆ (X j).hood C) (hloc : ∀ j, (X j).Local)
    (hPAD : ∀ j i Z, Z ∉ G → (X j).bad i Z)
    (hone : ∀ j, (∀ p, Y j p ∈ G) →
      ∀ (k : I → ℕ) i, (∀ l, 1 ≤ k l) → k i = 1 → (X j).W k i ∈ G)
    (hSO : ∀ k, 1 ≤ k → k ≤ s → ∀ i,
      Y k (.inl i) = v k • Y 0 (.inl i) +
        ∑ j ∈ range k, α k j • (X j).W ((X j).run (k₀ j) univ) i)
    (hY0 : ∀ p, Y 0 p ∈ G)
    (hghost : ∀ k, (∀ i, Y k (.inl i) ∈ G) → ∀ p, Y k p ∈ G) :
    (∀ k ≤ s, ∀ p, Y k p ∈ G) ∧
      ∀ j < s, ∀ i, (X j).W ((X j).run (k₀ j) univ) i ∈ G := by
  let Wf : ℕ → I ⊕ P → E := fun j p => p.elim (fun i => (X j).W ((X j).run (k₀ j) univ) i)
    (fun _ => Y j p)
  have hWf : ∀ j < s, (∀ p, Y j p ∈ G) → ∀ p, (∃ i, p = .inl i) → Wf j p ∈ G := by
    rintro j - hY p ⟨i, rfl⟩
    exact (X j).run_admissible (hhood j) (hloc j) (hPAD j) (hone j hY) (k₀ j) (hk₀ j) i
  have h := ssp_stages hG s (fun p => ∃ i, p = .inl i) Y Wf v α hv hα hsum
    (by rintro k h1 h2 p ⟨i, rfl⟩; exact hSO k h1 h2 i) hY0
    (fun k hk => hghost k fun i => hk _ ⟨i, rfl⟩) hWf
  refine ⟨fun k hk => (h k hk).1, fun j hj i => ?_⟩
  exact (h s le_rfl).2 j hj (.inl i) ⟨i, rfl⟩

/-- **Corollary 6.4 (order one everywhere).** If every substep of an admissible stage
is admissible (the first-order operator with aligned signs, Corollary 5.3 with
`τ = Δt/C`), every explicit RK method with `C > 0` preserves the admissible set. -/
theorem ssp_order_one {G : Set E} (hG : Convex ℝ G) (s : ℕ) (interior : P → Prop)
    (Y : ℕ → P → E) (W : ℕ → P → E) (v : ℕ → ℝ) (α : ℕ → ℕ → ℝ)
    (hv : ∀ k, 0 ≤ v k) (hα : ∀ k j, 0 ≤ α k j)
    (hsum : ∀ k, v k + ∑ j ∈ range k, α k j = 1)
    (hSO : ∀ k, 1 ≤ k → k ≤ s → ∀ i, interior i →
      Y k i = v k • Y 0 i + ∑ j ∈ range k, α k j • W j i)
    (hY0 : ∀ p, Y 0 p ∈ G)
    (hghost : ∀ k, (∀ i, interior i → Y k i ∈ G) → ∀ p, Y k p ∈ G)
    (hfirst : ∀ j, (∀ p, Y j p ∈ G) → ∀ i, interior i → W j i ∈ G) :
    ∀ k ≤ s, ∀ p, Y k p ∈ G := fun k hk =>
  (ssp_stages hG s interior Y W v α hv hα hsum hSO hY0 hghost
    (fun j _ => hfirst j) k hk).1

end Stages

end Meshfree
