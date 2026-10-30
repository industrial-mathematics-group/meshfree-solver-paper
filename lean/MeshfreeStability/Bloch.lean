import MeshfreeStability.Lattice

/-!
# Section 6: periodic clouds, Bloch reduction

The block-circulant structure `eq:blockcirc` and the unitary equivalence of `L_ℓ` with
`ℓ ⊕_θ Â(θ)` (discrete Fourier transform in the cell index) give the norm identity
`eq:blochnorm`, `‖e^{tL_ℓ}‖ = max_{θ∈Θ_ℓ} ‖e^{tℓÂ(θ)}‖`. **This identity is a hypothesis here**
(`hnorm`); the DFT diagonalisation is not formalized. What is formalized is everything the
theorem derives from it:

* **Theorem 6.1**, `eq:KY` and the stability criterion: `bloch_bound_iff` (for every `C`,
  `‖e^{tL_ℓ}‖ ≤ C` for all `ℓ, t` iff `‖e^{sÂ(θ)}‖ ≤ C` for all `θ, s`, so the two suprema in
  `eq:KY` agree) and `bloch_stable_iff` (stable for *some* `C, ω` iff `𝒦_Y < ∞`, and then with
  `ω = 0`). The density/semicontinuity step is done with closed sublevel sets.
* **Corollary 6.4** (instability): `bloch_unstable`, with `‖e^{sM}‖ ≥ e^{s α(M)}` and the
  continuity of the spectral abscissa as hypotheses.
* **Proposition 6.3** (sufficient condition) is **not formalized** (it uses analytic perturbation
  theory of eigenvalues, Kato Ch. II).
-/

open Filter Topology Real

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

variable {T : Type*} [TopologicalSpace T]

/-- **Theorem 6.1, `eq:KY`.** `N ℓ t = ‖e^{tL_ℓ}‖_V`, `g s θ = ‖e^{sÂ(θ)}‖_{V_Y}`, `Θ ℓ` the
sampled wave numbers. Hypotheses: the norm identity `eq:blochnorm` for `ℓ > ℓ₀` (`hnorm`:
`N ℓ t` is the maximum of `g (tℓ)` over `Θ ℓ`), `Θ ℓ ⊆ Θ (jℓ)`, density of `⋃_{ℓ>ℓ₀} Θ ℓ`, and
continuity of `g s` in `θ`. Then a bound `C` holds for all `ℓ, t` iff it holds for all `θ, s`. -/
theorem bloch_bound_iff (N : ℕ → ℝ → ℝ) (g : ℝ → T → ℝ) (Θ : ℕ → Set T) (ℓ₀ : ℕ)
    (hnorm : ∀ ℓ > ℓ₀, ∀ t, 0 ≤ t → IsGreatest ((fun θ => g (t * ℓ) θ) '' Θ ℓ) (N ℓ t))
    (hmult : ∀ ℓ j : ℕ, 1 ≤ j → Θ ℓ ⊆ Θ (j * ℓ))
    (hdense : Dense (⋃ ℓ > ℓ₀, Θ ℓ)) (hcont : ∀ s, Continuous (g s)) (C : ℝ) :
    (∀ ℓ > ℓ₀, ∀ t, 0 ≤ t → N ℓ t ≤ C) ↔ ∀ θ, ∀ s, 0 ≤ s → g s θ ≤ C := by
  constructor
  · intro hN θ s hs
    -- the sublevel set is closed and contains the dense set
    have hcl : IsClosed {θ | g s θ ≤ C} := isClosed_le (hcont s) continuous_const
    have hsub : (⋃ ℓ > ℓ₀, Θ ℓ) ⊆ {θ | g s θ ≤ C} := by
      intro θ' hθ'
      simp only [Set.mem_iUnion] at hθ'
      obtain ⟨ℓ, hℓ, hθℓ⟩ := hθ'
      have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (Nat.zero_le ℓ₀).trans_lt hℓ
      have := (hnorm ℓ hℓ (s / ℓ) (div_nonneg hs hℓpos.le)).2 ⟨θ', hθℓ, rfl⟩
      show g s θ' ≤ C
      rw [div_mul_cancel₀ s hℓpos.ne'] at this
      exact this.trans (hN ℓ hℓ _ (div_nonneg hs hℓpos.le))
    have := hcl.closure_subset_iff.2 hsub
    rw [hdense.closure_eq] at this
    exact this (Set.mem_univ θ)
  · intro hg ℓ hℓ t ht
    obtain ⟨⟨θ, _, hθ⟩, _⟩ := hnorm ℓ hℓ t ht
    rw [← hθ]
    have hℓpos : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    exact hg θ _ (mul_nonneg ht hℓpos)

/-- **Theorem 6.1, stability criterion.** The refinement family is stable for *some* `C, ω`
(`‖e^{tL_ℓ}‖ ≤ C e^{ωt}`) iff `𝒦_Y < ∞` (a uniform bound `g s θ ≤ K`), and then it is stable with
`C = K`, `ω = 0`. -/
theorem bloch_stable_iff (N : ℕ → ℝ → ℝ) (g : ℝ → T → ℝ) (Θ : ℕ → Set T) (ℓ₀ : ℕ)
    (hnorm : ∀ ℓ > ℓ₀, ∀ t, 0 ≤ t → IsGreatest ((fun θ => g (t * ℓ) θ) '' Θ ℓ) (N ℓ t))
    (hmult : ∀ ℓ j : ℕ, 1 ≤ j → Θ ℓ ⊆ Θ (j * ℓ))
    (hdense : Dense (⋃ ℓ > ℓ₀, Θ ℓ)) (hcont : ∀ s, Continuous (g s)) :
    (∃ C ω : ℝ, ∀ ℓ > ℓ₀, ∀ t, 0 ≤ t → N ℓ t ≤ C * Real.exp (ω * t)) ↔
      ∃ K, ∀ θ, ∀ s, 0 ≤ s → g s θ ≤ K := by
  constructor
  · rintro ⟨C, ω, hN⟩
    refine ⟨C, fun θ s hs => ?_⟩
    have hcl : IsClosed {θ | g s θ ≤ C} := isClosed_le (hcont s) continuous_const
    have hsub : (⋃ ℓ > ℓ₀, Θ ℓ) ⊆ {θ | g s θ ≤ C} := by
      intro θ' hθ'
      simp only [Set.mem_iUnion] at hθ'
      obtain ⟨ℓ₁, hℓ₁, hθℓ⟩ := hθ'
      show g s θ' ≤ C
      -- `θ' ∈ Θ (j ℓ₁)` for every `j ≥ 1`, and `e^{ω s/(jℓ₁)} → 1`
      have hb : ∀ j : ℕ, 1 ≤ j → g s θ' ≤ C * Real.exp (ω * (s / ((j * ℓ₁ : ℕ) : ℝ))) := by
        intro j hj
        have hjℓ : j * ℓ₁ > ℓ₀ := lt_of_lt_of_le hℓ₁ (Nat.le_mul_of_pos_left ℓ₁ hj)
        have hpos : (0 : ℝ) < ((j * ℓ₁ : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le ℓ₀).trans_lt hjℓ
        have := (hnorm _ hjℓ (s / ((j * ℓ₁ : ℕ) : ℝ)) (div_nonneg hs hpos.le)).2
          ⟨θ', hmult ℓ₁ j hj hθℓ, rfl⟩
        rw [div_mul_cancel₀ s hpos.ne'] at this
        exact this.trans (hN _ hjℓ _ (div_nonneg hs hpos.le))
      have hlim : Tendsto (fun j : ℕ => C * Real.exp (ω * (s / ((j * ℓ₁ : ℕ) : ℝ)))) atTop
          (𝓝 (C * Real.exp (ω * 0))) := by
        refine (tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp
          (tendsto_const_nhds.mul ?_)))
        have hℓ₁ : (0 : ℝ) < ℓ₁ := by exact_mod_cast (Nat.zero_le ℓ₀).trans_lt hℓ₁
        have : Tendsto (fun j : ℕ => ((j * ℓ₁ : ℕ) : ℝ)) atTop atTop := by
          push_cast
          exact Tendsto.atTop_mul_const hℓ₁ tendsto_natCast_atTop_atTop
        exact tendsto_const_nhds.div_atTop this
      rw [mul_zero, Real.exp_zero, mul_one] at hlim
      exact ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun j hj => hb j hj⟩)
    have := hcl.closure_subset_iff.2 hsub
    rw [hdense.closure_eq] at this
    exact this (Set.mem_univ θ)
  · rintro ⟨K, hK⟩
    refine ⟨K, 0, fun ℓ hℓ t ht => ?_⟩
    rw [zero_mul, Real.exp_zero, mul_one]
    exact (bloch_bound_iff N g Θ ℓ₀ hnorm hmult hdense hcont K).2 hK ℓ hℓ t ht

/-- **Corollary 6.4 (instability).** If the spectral abscissa `α(Â(θ))` is continuous at `θ*`
with `α(Â(θ*)) > 0`, if `‖e^{sM}‖ ≥ e^{s α(M)}` (eigenvector of the eigenvalue with largest real
part), and if every neighbourhood of `θ*` meets `Θ ℓ` for all large `ℓ`, then there is `γ > 0`
with `‖e^{tL_ℓ}‖ ≥ e^{γ t ℓ}` for all large `ℓ` and all `t ≥ 0`. -/
theorem bloch_unstable (N : ℕ → ℝ → ℝ) (g : ℝ → T → ℝ) (Θ : ℕ → Set T) (ℓ₀ : ℕ)
    (hnorm : ∀ ℓ > ℓ₀, ∀ t, 0 ≤ t → IsGreatest ((fun θ => g (t * ℓ) θ) '' Θ ℓ) (N ℓ t))
    (α : T → ℝ) (θs : T) (hαc : ContinuousAt α θs) (hαpos : 0 < α θs)
    (hgα : ∀ θ, ∀ s, 0 ≤ s → Real.exp (s * α θ) ≤ g s θ)
    (happrox : ∀ U ∈ 𝓝 θs, ∀ᶠ ℓ : ℕ in atTop, (Θ ℓ ∩ U).Nonempty) :
    ∃ γ > 0, ∀ᶠ ℓ : ℕ in atTop, ∀ t, 0 ≤ t → Real.exp (γ * t * ℓ) ≤ N ℓ t := by
  refine ⟨α θs / 2, by positivity, ?_⟩
  have hU : {θ | α θs / 2 < α θ} ∈ 𝓝 θs :=
    hαc.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  filter_upwards [happrox _ hU, eventually_gt_atTop ℓ₀] with ℓ hℓ hℓ₀ t ht
  obtain ⟨θ, hθΘ, hθU⟩ := hℓ
  have hℓpos : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have h1 := (hnorm ℓ hℓ₀ t ht).2 ⟨θ, hθΘ, rfl⟩
  have h2 := hgα θ (t * ℓ) (mul_nonneg ht hℓpos)
  refine le_trans ?_ (h2.trans h1)
  apply Real.exp_le_exp.2
  have : α θs / 2 ≤ α θ := le_of_lt hθU
  have := mul_le_mul_of_nonneg_left this (mul_nonneg ht hℓpos)
  nlinarith

end Meshfree.Stability
