import MeshfreeStability.Markov

/-!
# Section 5: high order on lattices

* **Lemma 5.1** (skew-symmetric central part): translation-invariant operators on a finite
  abelian group (`conv`), `conv_transpose_odd`, `conv_transpose_even`, `odd_of_anticommute`,
  `even_of_commute`, `skew_qf_zero`, `lattice_contraction_iff`.
* **Theorem 5.2** (order two on lattices): (ii) `k2_nearest_neighbour`; (i) `k2_symbol_mu_form`
  (from `eq:rek2` to the `μ`-form), `k2_mu_form_eq` (the `E_{nm}` expansion), `E_eq_cheb`
  (Chebyshev form), `k2_lattice_1d` (non-positivity **given the computer-assisted inequalities
  `P_{nm} ≥ 0` on `[-1,1]` as a hypothesis**), `E12_closed_form`, `P11_nonneg`.
-/

open Finset Matrix Real

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

/-! ### Lemma 5.1 -/

section Skew

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A translation-invariant (convolution) operator with stencil `β`: `(CU)_i = ∑_l β_l U_{i+l}`,
as the matrix `C_{ij} = β_{j-i}`. -/
def conv (β : G → ℝ) : Matrix G G ℝ := fun i j => β (j - i)

theorem conv_mulVec (β : G → ℝ) (U : G → ℝ) (i : G) :
    (conv β *ᵥ U) i = ∑ l, β l * U (i + l) := by
  simp only [conv, mulVec, dotProduct]
  exact Fintype.sum_equiv (Equiv.subRight i) _ _ (fun j => by simp [add_sub_cancel])

/-- Odd stencil ⇒ skew-symmetric. -/
theorem conv_transpose_odd (β : G → ℝ) (hβ : ∀ l, β (-l) = -β l) : (conv β)ᵀ = -conv β := by
  ext i j; simp only [transpose_apply, conv, Matrix.neg_apply]; rw [← hβ, neg_sub]

/-- Even stencil ⇒ symmetric. -/
theorem conv_transpose_even (β : G → ℝ) (hβ : ∀ l, β (-l) = β l) : (conv β)ᵀ = conv β := by
  ext i j; simp only [transpose_apply, conv]; rw [← hβ, neg_sub]

/-- The point reflection `(RU)_i = U_{-i}`. -/
def refl (U : G → ℝ) : G → ℝ := fun i => U (-i)

/-- `CR = -RC` (the reflection identity of the proof of Lemma 5.1, which comes from the odd
weights and the reflection-equivariant fits) forces an odd stencil. -/
theorem odd_of_anticommute (β : G → ℝ)
    (h : ∀ U, conv β *ᵥ refl U = -refl (conv β *ᵥ U)) : ∀ l, β (-l) = -β l := by
  intro l
  have := congrFun (h (Pi.single (-l) 1)) 0
  simp only [conv_mulVec, refl, Pi.neg_apply, zero_add, neg_zero] at this
  simp only [Pi.single_apply, neg_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at this
  rw [this, neg_neg]

/-- `SR = RS` forces an even stencil. -/
theorem even_of_commute (β : G → ℝ)
    (h : ∀ U, conv β *ᵥ refl U = refl (conv β *ᵥ U)) : ∀ l, β (-l) = β l := by
  intro l
  have := congrFun (h (Pi.single (-l) 1)) 0
  simp only [conv_mulVec, refl, zero_add, neg_zero] at this
  simp only [Pi.single_apply, neg_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at this
  rw [this]

/-- A skew-symmetric matrix has zero energy. -/
theorem skew_qf_zero {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) (u : ι → ℝ) :
    qf C u = 0 := by
  have h1 : qf C u = qf Cᵀ u := by
    simp only [qf_eq_sum, transpose_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hC] at h1
  have : qf (-C) u = -qf C u := by simp [qf, neg_mulVec]
  linarith

/-- One-sided derivative test: a function with `f t ≤ f 0` for `t ≥ 0` has `f'(0) ≤ 0`. -/
theorem deriv_nonpos_of_le {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hle : ∀ t, 0 ≤ t → f t ≤ f 0) : d ≤ 0 := by
  have hs := hf.tendsto_slope_zero_right
  refine le_of_tendsto hs ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.le) (by linarith [hle t ht'.le])

/-- **Lemma 5.1, stability part.** For `L = C + S` with `C` skew-symmetric and `S` symmetric
(odd/even stencils), the semi-discrete scheme is a contraction in the unweighted (= volume) norm,
`|U(t)| ≤ |U(0)|` for all solutions, **if and only if** `S ≤ 0`. The "only if" uses existence of
solutions through every initial value (`hex`, provided by the matrix exponential). -/
theorem lattice_contraction_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (C S : Matrix ι ι ℝ)
    (hC : Cᵀ = -C) (hS : Sᵀ = S)
    (hex : ∀ v : ι → ℝ, ∃ U : ℝ → ι → ℝ, U 0 = v ∧ ∀ t, HasDerivAt U ((C + S) *ᵥ U t) t) :
    (∀ U : ℝ → ι → ℝ, (∀ t, HasDerivAt U ((C + S) *ᵥ U t) t) →
        ∀ t, 0 ≤ t → qf 1 (U t) ≤ qf 1 (U 0)) ↔ ∀ u, qf S u ≤ 0 := by
  have hqfL : ∀ u, u ⬝ᵥ (1 *ᵥ ((C + S) *ᵥ u)) = qf S u := by
    intro u
    have := skew_qf_zero C hC u
    simp only [one_mulVec, add_mulVec, dotProduct_add]
    simpa [qf] using this
  constructor
  · intro h v
    by_contra hv
    push_neg at hv
    obtain ⟨U, hU0, hU⟩ := hex v
    have hd := hasDerivAt_qf (W := (1 : Matrix ι ι ℝ)) transpose_one (hU 0)
    rw [hqfL, hU0] at hd
    have := deriv_nonpos_of_le hd (fun t ht => h U hU t ht)
    linarith
  · intro h U hU t ht
    have := energy_bound transpose_one (ω := 0) (fun u => by rw [hqfL, zero_mul]; exact h u) hU ht
    simpa using this

/-- `lattice_contraction_iff` with the existence of solutions discharged by the matrix
exponential. -/
theorem lattice_contraction_iff' {ι : Type*} [Fintype ι] [DecidableEq ι] (C S : Matrix ι ι ℝ)
    (hC : Cᵀ = -C) (hS : Sᵀ = S) :
    (∀ U : ℝ → ι → ℝ, (∀ t, HasDerivAt U ((C + S) *ᵥ U t) t) →
        ∀ t, 0 ≤ t → qf 1 (U t) ≤ qf 1 (U 0)) ↔ ∀ u, qf S u ≤ 0 :=
  lattice_contraction_iff C S hC hS (fun v => linear_ode_exists (C + S) v)

end Skew

/-! ### Theorem 5.2 -/

section K2

/-- **Theorem 5.2(ii)**: the nearest-neighbour bracket. -/
theorem k2_nearest_neighbour (θ : ℝ) :
    cos θ - 1 + (1 / 2) * sin θ ^ 2 = -(1 / 2) * (1 - cos θ) ^ 2 := by
  have := sin_sq_add_cos_sq θ; nlinarith [this]

/-- Theorem 5.2(ii) in `D` dimensions: `Re λ = -(1/2h) ∑_d |a_d| (1 - cos θ_d)² ≤ 0`. -/
theorem k2_nearest_neighbour_D {D : ℕ} (a θ : Fin D → ℝ) {h : ℝ} (hh : 0 < h) :
    (1 / h) * ∑ d, |a d| * (cos (θ d) - 1 + (1 / 2) * sin (θ d) ^ 2)
      = -(1 / (2 * h)) * ∑ d, |a d| * (1 - cos (θ d)) ^ 2 ∧
    (1 / h) * ∑ d, |a d| * (cos (θ d) - 1 + (1 / 2) * sin (θ d) ^ 2) ≤ 0 := by
  have e : (1 / h) * ∑ d, |a d| * (cos (θ d) - 1 + (1 / 2) * sin (θ d) ^ 2)
      = -(1 / (2 * h)) * ∑ d, |a d| * (1 - cos (θ d)) ^ 2 := by
    simp only [k2_nearest_neighbour, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by field_simp
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 ≤ ∑ d, |a d| * (1 - cos (θ d)) ^ 2 :=
    Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have : 0 < 1 / (2 * h) := by positivity
  nlinarith

/-- The 1-D form of `eq:rek2` on a lattice with offsets `±n` (`n = 1,…,m`) and
`c_{±n} = ±c_n`: `Re λ/|a| = 2 ∑_n c_n [cos nθ - 1 + ½ n S sin nθ]`,
`S = 2 ∑_n c_n sin nθ`. -/
noncomputable def rek2 (m : ℕ) (c : ℕ → ℝ) (θ : ℝ) : ℝ :=
  2 * ∑ n ∈ Icc 1 m, c n * (cos (n * θ) - 1 +
    (1 / 2) * n * (2 * ∑ k ∈ Icc 1 m, c k * sin (k * θ)) * sin (n * θ))

/-- The `μ`-form of the proof of Theorem 5.2(i), `t = θ/2`. -/
noncomputable def muForm (m : ℕ) (μ : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 m, n * μ n) * (∑ n ∈ Icc 1 m, μ n * (1 - cos (2 * n * t)))
    - (1 / 2) * (∑ n ∈ Icc 1 m, n * μ n * sin (2 * n * t)) * (∑ n ∈ Icc 1 m, μ n * sin (2 * n * t))

/-- From `eq:rek2` to the `μ`-form: with `μ_n = 2c_n` and `∑ n μ_n = 1` (the weights
`c_n = w_n n / M`, `M = 2∑ w_n n²`), `-Re λ/|a| = μ-form(θ/2)`. -/
theorem k2_symbol_mu_form (m : ℕ) (c : ℕ → ℝ) (hnorm : ∑ n ∈ Icc 1 m, n * (2 * c n) = 1)
    (θ : ℝ) : -rek2 m c θ = muForm m (fun n => 2 * c n) (θ / 2) := by
  unfold rek2 muForm
  have e : ∀ n : ℕ, 2 * (n : ℝ) * (θ / 2) = n * θ := fun n => by ring
  simp only [e, hnorm, one_mul]
  set S := ∑ k ∈ Icc 1 m, c k * sin (k * θ)
  have h2S : ∑ n ∈ Icc 1 m, 2 * c n * sin (n * θ) = 2 * S := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  have hA : ∑ n ∈ Icc 1 m, c n * (cos (n * θ) - 1 + 1 / 2 * n * (2 * S) * sin (n * θ))
      = ∑ n ∈ Icc 1 m, c n * (cos (n * θ) - 1) + (∑ n ∈ Icc 1 m, n * c n * sin (n * θ)) * S := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hB : ∑ n ∈ Icc 1 m, (n : ℝ) * (2 * c n) * sin (n * θ)
      = 2 * ∑ n ∈ Icc 1 m, n * c n * sin (n * θ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  have hC : ∑ n ∈ Icc 1 m, 2 * c n * (1 - cos (n * θ))
      = -(2 * ∑ n ∈ Icc 1 m, c n * (cos (n * θ) - 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hA, hB, hC, h2S]; ring

/-- `E_{nm}(t)` of the proof of Theorem 5.2(i). -/
noncomputable def Enm (n m : ℕ) (t : ℝ) : ℝ :=
  n * sin (m * t) ^ 2 + m * sin (n * t) ^ 2 - (n + m) * sin (n * t) * cos (n * t) * sin (m * t) * cos (m * t)

/-- The `μ`-form is the quadratic form `∑_{n,m} μ_n μ_m E_{nm}(t)` (any `μ`). -/
theorem k2_mu_form_eq (m : ℕ) (μ : ℕ → ℝ) (t : ℝ) :
    muForm m μ t = ∑ n ∈ Icc 1 m, ∑ k ∈ Icc 1 m, μ n * μ k * Enm n k t := by
  -- `1 - cos 2x = 2 sin² x`, `sin 2x = 2 sin x cos x`, then symmetrize
  have h1 : ∀ x : ℝ, 1 - cos (2 * x) = 2 * sin x ^ 2 := fun x => by
    rw [cos_two_mul, cos_sq']; ring
  have h2 : ∀ x : ℝ, sin (2 * x) = 2 * sin x * cos x := fun x => sin_two_mul x
  have e1 : ∀ n : ℕ, 2 * (n : ℝ) * t = 2 * (n * t) := fun n => by ring
  unfold muForm Enm
  simp only [e1, h1, h2, Finset.mul_sum, Finset.sum_mul]
  -- write everything as a double sum and symmetrize
  have hsym : ∀ f : ℕ → ℕ → ℝ, ∑ n ∈ Icc 1 m, ∑ k ∈ Icc 1 m, f n k
      = (1 / 2) * ∑ n ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (f n k + f k n) := by
    intro f
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun n k => f k n)]
    ring
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [hsym]
  conv_rhs => rw [hsym]
  congr 1
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => by ring

open Polynomial Polynomial.Chebyshev in
/-- The integer polynomial `P_{nm} = n U_{m-1}² + m U_{n-1}² - (n+m) U_{n-1} T_n U_{m-1} T_m`
evaluated at `c`. -/
noncomputable def Pnm (n m : ℕ) (c : ℝ) : ℝ :=
  n * (U ℝ ((m : ℤ) - 1)).eval c ^ 2 + m * (U ℝ ((n : ℤ) - 1)).eval c ^ 2
    - (n + m) * (U ℝ ((n : ℤ) - 1)).eval c * (T ℝ n).eval c * (U ℝ ((m : ℤ) - 1)).eval c
      * (T ℝ m).eval c

open Polynomial Polynomial.Chebyshev in
/-- `E_{nm}(t) = sin² t · P_{nm}(cos t)`. -/
theorem E_eq_cheb (n m : ℕ) (t : ℝ) : Enm n m t = sin t ^ 2 * Pnm n m (cos t) := by
  have hs : ∀ k : ℕ, sin (k * t) = (U ℝ ((k : ℤ) - 1)).eval (cos t) * sin t := by
    intro k
    rw [U_real_cos]; congr 1; push_cast; ring
  have hc : ∀ k : ℕ, cos (k * t) = (T ℝ k).eval (cos t) := by
    intro k; rw [T_real_cos]; push_cast; ring
  unfold Enm Pnm
  rw [hs n, hs m, hc n, hc m]
  ring

/-- **Theorem 5.2(i), given the computer-assisted certificate.** Hypothesis `hP`: for
`1 ≤ k ≤ n ≤ 9`, `P_{nk} ≥ 0` on `[-1,1]` (verified in exact rational arithmetic by
`certify_K2_1d.py`; not re-checked in Lean). Then for every `m ≤ 9` and all `μ ≥ 0` the
`μ`-form is non-negative, i.e. `Re λ(θ) ≤ 0`. -/
theorem k2_lattice_1d (m : ℕ) (hm : m ≤ 9) (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n)
    (hP : ∀ n k : ℕ, 1 ≤ k → k ≤ n → n ≤ 9 → ∀ c ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ Pnm n k c)
    (t : ℝ) : 0 ≤ muForm m μ t := by
  rw [k2_mu_form_eq]
  have hc : cos t ∈ Set.Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos t, cos_le_one t⟩
  have hsym : ∀ n k, Pnm n k (cos t) = Pnm k n (cos t) := by
    intro n k; unfold Pnm; ring
  refine Finset.sum_nonneg fun n hn => Finset.sum_nonneg fun k hk => ?_
  rw [Finset.mem_Icc] at hn hk
  rw [E_eq_cheb]
  refine mul_nonneg (mul_nonneg (hμ n) (hμ k)) (mul_nonneg (sq_nonneg _) ?_)
  rcases le_total k n with h | h
  · exact hP n k hk.1 h (by omega) _ hc
  · rw [hsym]; exact hP k n hn.1 h (by omega) _ hc

/-- Theorem 5.2(i) in terms of the scheme's symbol `eq:rek2`. -/
theorem k2_lattice_1d_symbol (m : ℕ) (hm : m ≤ 9) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hnorm : ∑ n ∈ Icc 1 m, n * (2 * c n) = 1)
    (hP : ∀ n k : ℕ, 1 ≤ k → k ≤ n → n ≤ 9 → ∀ c ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ Pnm n k c)
    (θ : ℝ) : rek2 m c θ ≤ 0 := by
  have := k2_lattice_1d m hm (fun n => 2 * c n) (fun n => by have := hc n; positivity) hP (θ / 2)
  rw [← k2_symbol_mu_form m c hnorm] at this
  linarith

/-- The example of the proof: `E_{12}(t) = 2 sin² t (6c²+1)(1-c²)`, `c = cos t`. -/
theorem E12_closed_form (t : ℝ) :
    Enm 1 2 t = 2 * sin t ^ 2 * (6 * cos t ^ 2 + 1) * (1 - cos t ^ 2) := by
  unfold Enm
  push_cast
  rw [show (2 : ℝ) * t = 2 * t from rfl, sin_two_mul, cos_two_mul]
  simp only [one_mul]
  have := sin_sq_add_cos_sq t
  have hs : sin t ^ 2 = 1 - cos t ^ 2 := by linarith
  ring_nf

/-- A sample of the certificate checked in Lean: `P_{11} = 2(1 - c²) ≥ 0` on `[-1,1]`, and
`P_{21} = 2(6c²+1)(1-c²) ≥ 0`. -/
theorem P11_P21_nonneg (c : ℝ) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ Pnm 1 1 c ∧ 0 ≤ Pnm 2 1 c := by
  have h1 : 0 ≤ 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
  simp only [Pnm]
  norm_num [Polynomial.Chebyshev.U_zero, Polynomial.Chebyshev.U_one,
    Polynomial.Chebyshev.T_one, Polynomial.Chebyshev.T_two]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg c, mul_nonneg h1 (sq_nonneg c)]

end K2

end Meshfree.Stability
