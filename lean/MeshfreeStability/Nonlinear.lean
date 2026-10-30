import MeshfreeStability.Energy

/-!
# Section 3: nonlinear stability from positivity

* **Theorem 3.1** (maximum principle of stage-wise MOOD): `dmp_checkpoint`,
  `scalar_led_local_range`, `stagewise_mood_max_principle`.
* **Proposition 3.3** (`ℓ¹` bounds for Euler): `euler_l1_bounds`, `euler_l1_bounds_defect`.
* **Proposition 3.5** (local entropy inequality): `local_entropy_inequality`.
* **Corollary 3.7** (global entropy balance): `global_entropy_balance`,
  `global_entropy_nonincreasing`, `ssp_convex_functional`.
-/

open Finset

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

/-! ### Theorem 3.1 -/

section MaxPrinciple

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **One checkpoint with the strict DMP (`δ = 0`, no overrides).** If the detection flags
exactly the substeps outside the local range `[lo i, hi i]` (possibly together with PAD, which
can only flag more), and every particle at order one has its substep in its local range (the
LED property of the first-order operator, `scalar_led_local_range`), then the checkpoint ends with
every substep in its local range, for any initial orders. -/
theorem dmp_checkpoint (X : Checkpoint I ℝ) (lo hi : I → ℝ)
    (hbad : ∀ i Z, Z ∉ Set.Icc (lo i) (hi i) → X.bad i Z)
    (hhood : ∀ C, C ⊆ X.hood C) (hloc : X.Local)
    (hone : ∀ (k : I → ℕ) i, (∀ l, 1 ≤ k l) → k i = 1 → X.W k i ∈ Set.Icc (lo i) (hi i))
    (k₀ : I → ℕ) (hk₀ : ∀ i, 1 ≤ k₀ i) :
    ∀ i, X.W (X.run k₀ univ) i ∈ Set.Icc (lo i) (hi i) := by
  obtain ⟨hk, hspec⟩ := X.run_spec hhood hloc _ k₀ univ rfl hk₀
    (fun i hi => absurd (mem_univ i) hi)
  intro i
  by_contra hW
  exact hW (hone _ i hk (hspec i (hbad i _ hW)))

/-- The local range of the DMP: minimum and maximum of `Y` over the closed neighbourhood. -/
noncomputable def lrange {Q : Type*} (cn : Finset Q) (hne : cn.Nonempty) (Y : Q → ℝ) :
    ℝ × ℝ := (cn.inf' hne Y, cn.sup' hne Y)

theorem lrange_subset {Q : Type*} (cn : Finset Q) (hne : cn.Nonempty) (Y : Q → ℝ) {m M : ℝ}
    (hY : ∀ q, Y q ∈ Set.Icc m M) :
    m ≤ (lrange cn hne Y).1 ∧ (lrange cn hne Y).2 ≤ M := by
  constructor
  · exact Finset.le_inf' hne _ fun q _ => (hY q).1
  · exact Finset.sup'_le hne _ fun q _ => (hY q).2

/-- **The first-order substep stays in the local range** (Corollary 5.3 of [A], scalar part):
with zero-sum weights, aligned signs, `|a| ≤ s` for the divided differences of the fluxes
(hypothesis (M3)) and `2τ∑ s|c| ≤ 1` (M6), the update lies between the minimum and maximum
over the closed neighbourhood. This discharges `hone` in `dmp_checkpoint`. -/
theorem scalar_led_local_range {Q : Type*} {D : ℕ} {J : Type*} [Fintype J]
    (cn : Finset Q) (hne : cn.Nonempty) (Y : Q → ℝ) (i : Q) (hi : i ∈ cn) (nbr : J → Q)
    (hnbr : ∀ j, nbr j ∈ cn) (F : Fin D → ℝ → ℝ) (c s a : J → Fin D → ℝ)
    (ha0 : ∀ d, ∑ j, c j d = 0)
    (hquot : ∀ j d, F d (Y (nbr j)) - F d (Y i) = a j d * (Y (nbr j) - Y i))
    (has : ∀ j d, |a j d| ≤ s j d) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : 2 * τ * ∑ j, ∑ d, s j d * |c j d| ≤ 1) :
    Y i + τ * schemeOp F c (fun j d => Real.sign (c j d)) s (Y i) (fun _ => Y i)
      (fun j => Y (nbr j)) ∈ Set.Icc (lrange cn hne Y).1 (lrange cn hne Y).2 := by
  have h := scalar_led F c s a (Y i) (fun j => Y (nbr j)) ha0 hquot has hτ hcfl
    (lo := (lrange cn hne Y).1) (hi := (lrange cn hne Y).2)
    ⟨Finset.inf'_le _ hi, fun j => Finset.inf'_le _ (hnbr j)⟩
    ⟨Finset.le_sup' _ hi, fun j => Finset.le_sup' _ (hnbr j)⟩
  exact ⟨h.1, h.2⟩

/-- **Theorem 3.1 (maximum principle of stage-wise MOOD).** Particles `I ⊕ P` (interior and
ghosts), stages `Y k`, checkpoints `X j` with the strict DMP relative to the closed
neighbourhoods `cn i` of `Y j`. Hypotheses: (M4) the detection flags every substep outside the
local range; first-order substeps are in the local range (`hone`, which is
`scalar_led_local_range` under (M1)–(M3), (M6)); Shu–Osher form with `C > 0` (Lemma 6.1 of
[A]); (M5) ghosts stay in `[m, M]`. Then all stages, hence all `Uⁿ`, stay in `[m, M]`, and every
checkpoint ends with all substeps in their local ranges. -/
theorem stagewise_mood_max_principle {P : Type*} (s : ℕ) (Y : ℕ → I ⊕ P → ℝ)
    (cn : I → Finset (I ⊕ P)) (hne : ∀ i, (cn i).Nonempty)
    (X : ℕ → Checkpoint I ℝ) (k₀ : ℕ → I → ℕ) (hk₀ : ∀ j i, 1 ≤ k₀ j i)
    (v : ℕ → ℝ) (α : ℕ → ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (hα : ∀ k j, 0 ≤ α k j)
    (hsum : ∀ k, v k + ∑ j ∈ range k, α k j = 1)
    (hhood : ∀ j C, C ⊆ (X j).hood C) (hloc : ∀ j, (X j).Local)
    (hbad : ∀ j i Z, Z ∉ Set.Icc (lrange (cn i) (hne i) (Y j)).1 (lrange (cn i) (hne i) (Y j)).2 →
      (X j).bad i Z)
    (hone : ∀ j (k : I → ℕ) i, (∀ l, 1 ≤ k l) → k i = 1 →
      (X j).W k i ∈ Set.Icc (lrange (cn i) (hne i) (Y j)).1 (lrange (cn i) (hne i) (Y j)).2)
    (hSO : ∀ k, 1 ≤ k → k ≤ s → ∀ i,
      Y k (.inl i) = v k • Y 0 (.inl i) +
        ∑ j ∈ range k, α k j • (X j).W ((X j).run (k₀ j) univ) i)
    {m M : ℝ} (hY0 : ∀ p, Y 0 p ∈ Set.Icc m M)
    (hghost : ∀ k, (∀ i, Y k (.inl i) ∈ Set.Icc m M) → ∀ p, Y k p ∈ Set.Icc m M) :
    (∀ k ≤ s, ∀ p, Y k p ∈ Set.Icc m M) ∧
      ∀ j < s, ∀ i, (X j).W ((X j).run (k₀ j) univ) i ∈
        Set.Icc (lrange (cn i) (hne i) (Y j)).1 (lrange (cn i) (hne i) (Y j)).2 := by
  -- every checkpoint ends in the local ranges
  have hloc_range : ∀ j i, (X j).W ((X j).run (k₀ j) univ) i ∈
      Set.Icc (lrange (cn i) (hne i) (Y j)).1 (lrange (cn i) (hne i) (Y j)).2 := by
    intro j
    obtain ⟨hk, hspec⟩ := (X j).run_spec (hhood j) (hloc j) _ (k₀ j) univ rfl (hk₀ j)
      (fun i hi => absurd (mem_univ i) hi)
    intro i
    by_contra hW
    exact hW (hone j _ i hk (hspec i (hbad j i _ hW)))
  let Wf : ℕ → I ⊕ P → ℝ := fun j p => p.elim (fun i => (X j).W ((X j).run (k₀ j) univ) i)
    (fun _ => Y j p)
  have hWf : ∀ j < s, (∀ p, Y j p ∈ Set.Icc m M) → ∀ p, (∃ i, p = .inl i) →
      Wf j p ∈ Set.Icc m M := by
    rintro j - hY p ⟨i, rfl⟩
    have h1 := hloc_range j i
    have h2 := lrange_subset (cn i) (hne i) (Y j) hY
    exact ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩
  have h := ssp_stages (convex_Icc m M) s (fun p => ∃ i, p = .inl i) Y Wf v α hv hα hsum
    (by rintro k h1 h2 p ⟨i, rfl⟩; exact hSO k h1 h2 i) hY0
    (fun k hk => hghost k fun i => hk _ ⟨i, rfl⟩) hWf
  exact ⟨fun k hk => (h k hk).1, fun j _ i => hloc_range j i⟩

end MaxPrinciple

/-! ### Proposition 3.3 -/

section EulerL1

open Euler

variable {D : ℕ} {ι : Type*} [Fintype ι]

theorem Euler.ener_ge {γ : ℝ} (hγ : 1 < γ) {U : State D} (hU : U ∈ Adm γ) :
    pres γ U / (γ - 1) ≤ ener U ∧ msq U ≤ 2 * rho U * ener U ∧ 0 < ener U := by
  obtain ⟨hρ, hp⟩ := hU
  have hγ1 : 0 < γ - 1 := by linarith
  have hE : ener U = pres γ U / (γ - 1) + msq U / (2 * rho U) := by
    unfold pres; field_simp; ring
  have hm : 0 ≤ msq U := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : 0 ≤ msq U / (2 * rho U) := by positivity
  have h2 : 0 < pres γ U / (γ - 1) := by positivity
  refine ⟨by linarith, ?_, by linarith⟩
  have : msq U = 2 * rho U * (msq U / (2 * rho U)) := by field_simp
  have h3 : msq U / (2 * rho U) ≤ ener U := by linarith
  nlinarith

/-- **Proposition 3.3 (`ℓ¹` bounds from positivity).** If all states are admissible (as
Theorem 6.3 of [A] guarantees) and `V > 0`, with `𝓜_ρ = ∑ V_i ρ_i` and `𝓜_E = ∑ V_i E_i`:
`∑ V|ρ| = 𝓜_ρ`, `∑ V|E| = 𝓜_E`, `∑ V|m| ≤ √(2 𝓜_ρ 𝓜_E)` and `∑ V p/(γ-1) ≤ 𝓜_E`. -/
theorem euler_l1_bounds {γ : ℝ} (hγ : 1 < γ) (V : ι → ℝ) (hV : ∀ i, 0 < V i)
    (U : ι → State D) (hU : ∀ i, U i ∈ Adm γ) :
    ∑ i, V i * |rho (U i)| = ∑ i, V i * rho (U i) ∧
    ∑ i, V i * |ener (U i)| = ∑ i, V i * ener (U i) ∧
    ∑ i, V i * Real.sqrt (msq (U i)) ≤
      Real.sqrt (2 * (∑ i, V i * rho (U i)) * ∑ i, V i * ener (U i)) ∧
    ∑ i, V i * (pres γ (U i) / (γ - 1)) ≤ ∑ i, V i * ener (U i) := by
  have hE := fun i => Euler.ener_ge hγ (hU i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.sum_congr rfl fun i _ => by rw [abs_of_pos (hU i).1]
  · exact Finset.sum_congr rfl fun i _ => by rw [abs_of_pos (hE i).2.2]
  · -- `|m_i| ≤ √(2ρ_i E_i)` and Cauchy–Schwarz
    have hρ := fun i => (hU i).1
    calc ∑ i, V i * Real.sqrt (msq (U i))
        ≤ ∑ i, Real.sqrt (2 * V i * rho (U i)) * Real.sqrt (V i * ener (U i)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Real.sqrt_mul (by have := hV i; have := hρ i; positivity)]
          have hm := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hE i).2.1
            (sq_nonneg (V i)))
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hV i).le] at hm
          calc V i * Real.sqrt (msq (U i)) ≤ Real.sqrt (V i ^ 2 * (2 * rho (U i) * ener (U i))) := hm
            _ = _ := by ring_nf
      _ ≤ Real.sqrt (∑ i, 2 * V i * rho (U i)) * Real.sqrt (∑ i, V i * ener (U i)) := by
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
            (fun i => Real.sqrt (2 * V i * rho (U i))) (fun i => Real.sqrt (V i * ener (U i)))
          have e1 : ∀ i ∈ univ, Real.sqrt (2 * V i * rho (U i)) ^ 2 = 2 * V i * rho (U i) :=
            fun i _ => Real.sq_sqrt (by have := hV i; have := hρ i; positivity)
          have e2 : ∀ i ∈ univ, Real.sqrt (V i * ener (U i)) ^ 2 = V i * ener (U i) :=
            fun i _ => Real.sq_sqrt (by have := hV i; have := (hE i).2.2; positivity)
          rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at hcs
          rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => by
            have := hV i; have := hρ i; positivity)]
          exact Real.le_sqrt_of_sq_le hcs
      _ = Real.sqrt (2 * (∑ i, V i * rho (U i)) * ∑ i, V i * ener (U i)) := by
          rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => by
            have := hV i; have := hρ i; positivity)]
          have e : ∑ i, 2 * V i * rho (U i) = 2 * ∑ i, V i * rho (U i) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
          rw [e]
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE i).1 (hV i).le

/-- **Proposition 3.3(ii).** With the a-posteriori defect `𝓜ⁿ = 𝓜⁰ + Δⁿ`, the bounds hold with
`𝓜⁰ + |Δⁿ|`. Part (i) is the case `Δ = 0` (antisymmetric volume-weighted weights, [A] Prop. 4.4,
`ConsData.local_conservation`). -/
theorem euler_l1_bounds_defect {γ : ℝ} (hγ : 1 < γ) (V : ι → ℝ) (hV : ∀ i, 0 < V i)
    (U : ι → State D) (hU : ∀ i, U i ∈ Adm γ) {Mρ0 ME0 Δρ ΔE : ℝ}
    (hρ : ∑ i, V i * rho (U i) = Mρ0 + Δρ) (hE : ∑ i, V i * ener (U i) = ME0 + ΔE) :
    ∑ i, V i * |rho (U i)| ≤ Mρ0 + |Δρ| ∧ ∑ i, V i * |ener (U i)| ≤ ME0 + |ΔE| ∧
    ∑ i, V i * Real.sqrt (msq (U i)) ≤ Real.sqrt (2 * (Mρ0 + |Δρ|) * (ME0 + |ΔE|)) ∧
    ∑ i, V i * (pres γ (U i) / (γ - 1)) ≤ ME0 + |ΔE| := by
  obtain ⟨h1, h2, h3, h4⟩ := euler_l1_bounds hγ V hV U hU
  have hρ0 : 0 ≤ ∑ i, V i * rho (U i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hV i).le (hU i).1.le
  have hE0 : 0 ≤ ∑ i, V i * ener (U i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hV i).le (Euler.ener_ge hγ (hU i)).2.2.le
  have a1 : ∑ i, V i * rho (U i) ≤ Mρ0 + |Δρ| := by rw [hρ]; linarith [le_abs_self Δρ]
  have a2 : ∑ i, V i * ener (U i) ≤ ME0 + |ΔE| := by rw [hE]; linarith [le_abs_self ΔE]
  refine ⟨h1 ▸ a1, h2 ▸ a2, h3.trans (Real.sqrt_le_sqrt ?_), h4.trans a2⟩
  exact mul_le_mul (by linarith) a2 hE0 (by linarith)

end EulerL1

/-! ### Proposition 3.5 and Corollary 3.7 -/

section Entropy

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {D : ℕ} {J : Type*} [Fintype J]

/-- The first-order aligned operator `eq:L1` with piecewise constant states:
`∑_{j,d} [ s|c|(U_j - U_i) - c (F_d(U_j) - F_d(U_i)) ]`. -/
def L1 (F : Fin D → E → E) (c s : J → Fin D → ℝ) (Ui : E) (Uj : J → E) : E :=
  ∑ j, ∑ d, ((s j d * |c j d|) • (Uj j - Ui) - c j d • (F d (Uj j) - F d Ui))

/-- The scalar right-hand side of the entropy inequality `eq:entropy`: the same operator for the
pair `(η, q)`. -/
def L1scalar (eta : E → ℝ) (q : Fin D → E → ℝ) (c s : J → Fin D → ℝ) (Ui : E) (Uj : J → E) : ℝ :=
  ∑ j, ∑ d, (s j d * |c j d| * (eta (Uj j) - eta Ui) - c j d * (q d (Uj j) - q d Ui))

/-- The Riemann average `Ū_{ij,d} = ½(U_i+U_j) - σ(F_d(U_j)-F_d(U_i))/(2s)`, `σ = sgn c`. -/
noncomputable def riemannAvg (F : E → E) (c s : ℝ) (Ui Uj : E) : E :=
  (1 / 2 : ℝ) • (Ui + Uj) - (Real.sign c / (2 * s)) • (F Uj - F Ui)

theorem riemannAvg_identity (F : E → E) (c s : ℝ) (Ui Uj : E) (hs : 0 < s) :
    (2 * s * |c|) • (riemannAvg F c s Ui Uj - Ui) = (s * |c|) • (Uj - Ui) - c • (F Uj - F Ui) := by
  unfold riemannAvg
  have h1 : 2 * s * |c| * (Real.sign c / (2 * s)) = c := by
    rw [← ConsData.sign_mul_self c]; field_simp
    rcases lt_trichotomy c 0 with h | h | h
    · rw [Real.sign_of_neg h]; ring
    · subst h; simp
    · rw [Real.sign_of_pos h]; ring
  rw [smul_sub, smul_sub, smul_smul, smul_smul, h1]
  have : 2 * s * |c| * (1 / 2) = s * |c| := by ring
  rw [this]; module

/-- **Proposition 3.5 (local entropy inequality).** The Riemann-problem facts are hypotheses
(`hRiem`): for every edge with `c ≠ 0`, the Riemann average `Ū` is admissible (Harten–Lax–van Leer:
it is the cell average of the Riemann solution, whose fan is bounded by `s`, and `Ad` is convex and
invariant) and `η(Ū) ≤ ½(η(U_i)+η(U_j)) - σ(q_d(U_j)-q_d(U_i))/(2s)` (integrated entropy inequality
plus Jensen). Under `2τ ∑ s|c| ≤ 1` the update is admissible and satisfies `eq:entropy`. -/
theorem local_entropy_inequality {Ad : Set E} (hAd : Convex ℝ Ad) {eta : E → ℝ}
    (heta : ConvexOn ℝ Ad eta) (F : Fin D → E → E) (q : Fin D → E → ℝ)
    (c s : J → Fin D → ℝ) (Ui : E) (Uj : J → E) (hspos : ∀ j d, 0 < s j d)
    (hUi : Ui ∈ Ad)
    (hRiem : ∀ j d, c j d ≠ 0 →
      riemannAvg (F d) (c j d) (s j d) Ui (Uj j) ∈ Ad ∧
      eta (riemannAvg (F d) (c j d) (s j d) Ui (Uj j)) ≤ (1 / 2) * (eta Ui + eta (Uj j))
        - Real.sign (c j d) / (2 * s j d) * (q d (Uj j) - q d Ui))
    {τ : ℝ} (hτ : 0 ≤ τ) (hcfl : 2 * τ * ∑ j, ∑ d, s j d * |c j d| ≤ 1) :
    Ui + τ • L1 F c s Ui Uj ∈ Ad ∧
      eta (Ui + τ • L1 F c s Ui Uj) ≤ eta Ui + τ * L1scalar eta q c s Ui Uj := by
  classical
  -- points and weights of the convex combination
  let pt : Option (J × Fin D) → E := fun o => o.elim Ui fun p =>
    if c p.1 p.2 = 0 then Ui else riemannAvg (F p.2) (c p.1 p.2) (s p.1 p.2) Ui (Uj p.1)
  let β : J × Fin D → ℝ := fun p => 2 * τ * (s p.1 p.2 * |c p.1 p.2|)
  let wt : Option (J × Fin D) → ℝ := fun o => o.elim (1 - ∑ p, β p) β
  have hβ : ∀ p, 0 ≤ β p := fun p => by
    have := hspos p.1 p.2; simp only [β]; positivity
  have hsumβ : ∑ p, β p = 2 * τ * ∑ j, ∑ d, s j d * |c j d| := by
    simp only [β, ← Finset.mul_sum, Fintype.sum_prod_type]
  have hw0 : ∀ o ∈ (univ : Finset (Option (J × Fin D))), 0 ≤ wt o := by
    intro o _; cases o with
    | none => simp only [wt, Option.elim]; linarith
    | some p => exact hβ p
  have hw1 : ∑ o, wt o = 1 := by simp [wt, Fintype.sum_option]
  have hmem : ∀ o ∈ (univ : Finset (Option (J × Fin D))), pt o ∈ Ad := by
    intro o _; cases o with
    | none => exact hUi
    | some p =>
      simp only [pt, Option.elim]
      split_ifs with h
      · exact hUi
      · exact (hRiem p.1 p.2 h).1
  -- the update is the convex combination
  have hterm : ∀ p : J × Fin D, β p • (pt (some p) - Ui) =
      τ • ((s p.1 p.2 * |c p.1 p.2|) • (Uj p.1 - Ui) - c p.1 p.2 • (F p.2 (Uj p.1) - F p.2 Ui)) := by
    intro ⟨j, d⟩
    simp only [pt, Option.elim, β]
    split_ifs with h
    · simp [h]
    · rw [← riemannAvg_identity (F d) (c j d) (s j d) Ui (Uj j) (hspos j d), smul_smul]
      congr 1; ring
  have hupd : Ui + τ • L1 F c s Ui Uj = ∑ o, wt o • pt o := by
    rw [Fintype.sum_option]
    simp only [wt, pt, Option.elim]
    have : ∑ p, β p • (pt (some p) - Ui) = τ • L1 F c s Ui Uj := by
      simp only [hterm, L1, Finset.smul_sum, Fintype.sum_prod_type]
    rw [← this]
    simp only [pt, Option.elim, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  refine ⟨hupd ▸ hAd.sum_mem hw0 hw1 hmem, ?_⟩
  rw [hupd]
  refine (heta.map_sum_le hw0 hw1 hmem).trans ?_
  rw [Fintype.sum_option]
  simp only [wt, Option.elim, smul_eq_mul]
  -- bound each Riemann term
  have hp : ∀ p : J × Fin D, β p * eta (pt (some p)) ≤ β p * eta Ui +
      τ * (s p.1 p.2 * |c p.1 p.2| * (eta (Uj p.1) - eta Ui)
        - c p.1 p.2 * (q p.2 (Uj p.1) - q p.2 Ui)) := by
    intro ⟨j, d⟩
    simp only [pt, Option.elim, β]
    split_ifs with h
    · simp [h]
    · have hb := (hRiem j d h).2
      have hs := hspos j d
      have hc : Real.sign (c j d) * |c j d| = c j d := by
        rcases lt_trichotomy (c j d) 0 with h' | h' | h'
        · rw [Real.sign_of_neg h', abs_of_neg h']; ring
        · exact absurd h' h
        · rw [Real.sign_of_pos h', abs_of_pos h']; ring
      have hk : 0 ≤ 2 * τ * (s j d * |c j d|) := by positivity
      have := mul_le_mul_of_nonneg_left hb hk
      have e : 2 * τ * (s j d * |c j d|) * ((1 / 2) * (eta Ui + eta (Uj j))
          - Real.sign (c j d) / (2 * s j d) * (q d (Uj j) - q d Ui))
          = 2 * τ * (s j d * |c j d|) * eta Ui + τ * (s j d * |c j d| * (eta (Uj j) - eta Ui)
            - c j d * (q d (Uj j) - q d Ui)) := by
        clear_value pt β wt
        set a := |c j d|
        set sg := Real.sign (c j d)
        rw [← hc]; field_simp; ring
      linarith
  calc (1 - ∑ p, β p) * eta Ui + ∑ p, β p * eta (pt (some p))
      ≤ (1 - ∑ p, β p) * eta Ui + ∑ p, (β p * eta Ui + τ * (s p.1 p.2 * |c p.1 p.2| *
          (eta (Uj p.1) - eta Ui) - c p.1 p.2 * (q p.2 (Uj p.1) - q p.2 Ui))) := by
        gcongr with p _; exact hp p
    _ = eta Ui + τ * L1scalar eta q c s Ui Uj := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, L1scalar, Finset.mul_sum,
          Fintype.sum_prod_type]
        ring

/-- **Corollary 3.7, the summation identity.** On a periodic cloud (all particles interior,
symmetric neighbour relation, symmetric speeds, zero row sums), the volume-weighted sum of the
right-hand sides of `eq:entropy` is the pair-defect sum (ordered pairs, factor `½`):
`∑ V_i R_i = -½ ∑_i ∑_{j∈ν(i)} ∑_d [ d_{ij,d}(q_i+q_j) - s_{ij,d} e_{ij,d}(η_j-η_i) ]`
with `d = V_i c_{ij} + V_j c_{ji}`, `e = V_i|c_{ij}| - V_j|c_{ji}|`. -/
theorem global_entropy_balance {ι : Type*} [Fintype ι] [DecidableEq ι] (nb : ι → Finset ι)
    (hnb : ∀ i j, j ∈ nb i ↔ i ∈ nb j) (V : ι → ℝ) (c s : ι → ι → Fin D → ℝ)
    (hs : ∀ i j d, s j i d = s i j d) (hc0 : ∀ i d, ∑ j ∈ nb i, c i j d = 0)
    (et : ι → ℝ) (qq : Fin D → ι → ℝ) :
    ∑ i, V i * ∑ j ∈ nb i, ∑ d, (s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j - qq d i))
      = -(1 / 2) * ∑ i, ∑ j ∈ nb i, ∑ d,
          ((V i * c i j d + V j * c j i d) * (qq d i + qq d j)
            - s i j d * (V i * |c i j d| - V j * |c j i d|) * (et j - et i)) := by
  -- step 1: use zero row sums to replace `q_j - q_i` by `q_j + q_i`
  have h1 : ∀ i, ∑ j ∈ nb i, ∑ d, (s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j - qq d i))
      = ∑ j ∈ nb i, ∑ d, (s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j + qq d i)) := by
    intro i
    have hz : ∑ j ∈ nb i, ∑ d, c i j d * qq d i = 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun d _ => by rw [← Finset.sum_mul, hc0 i d, zero_mul]
    have : ∀ j d, s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j - qq d i)
        = (s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j + qq d i))
          + 2 * (c i j d * qq d i) := fun j d => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hz, mul_zero, add_zero]
  -- step 2: symmetrize over ordered pairs
  set f : ι → ι → ℝ := fun i j => V i * ∑ d, (s i j d * |c i j d| * (et j - et i)
    - c i j d * (qq d j + qq d i))
  have hswap : ∑ i, ∑ j ∈ nb i, f i j = ∑ i, ∑ j ∈ nb i, f j i := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [mem_sigma, mem_univ, true_and] at hp ⊢; exact (hnb _ _).1 hp
    · intro p hp; simp only [mem_sigma, mem_univ, true_and] at hp ⊢; exact (hnb _ _).1 hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; rfl
  have hpair : ∀ i j, f i j + f j i = -∑ d, ((V i * c i j d + V j * c j i d) * (qq d i + qq d j)
      - s i j d * (V i * |c i j d| - V j * |c j i d|) * (et j - et i)) := by
    intro i j
    simp only [f, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [hs j i]; ring
  calc ∑ i, V i * ∑ j ∈ nb i, ∑ d, (s i j d * |c i j d| * (et j - et i)
        - c i j d * (qq d j - qq d i))
      = ∑ i, ∑ j ∈ nb i, f i j := by
        simp only [h1, f, Finset.mul_sum]
    _ = (1 / 2) * (∑ i, ∑ j ∈ nb i, f i j + ∑ i, ∑ j ∈ nb i, f j i) := by rw [← hswap]; ring
    _ = _ := by
        clear_value f
        rw [← Finset.sum_add_distrib]
        have e : ∀ i, ∑ j ∈ nb i, f i j + ∑ j ∈ nb i, f j i = ∑ j ∈ nb i, (f i j + f j i) :=
          fun i => by rw [Finset.sum_add_distrib]
        simp only [e, hpair, Finset.sum_neg_distrib]
        ring

/-- **Corollary 3.7, antisymmetric case.** If the volume-weighted weights are antisymmetric,
`V_i c_{ij} = -V_j c_{ji}`, with `V > 0`, the pair defects vanish and the total entropy does not
increase under one forward Euler step satisfying the local entropy inequalities. -/
theorem global_entropy_nonincreasing {ι : Type*} [Fintype ι] [DecidableEq ι] (nb : ι → Finset ι)
    (hnb : ∀ i j, j ∈ nb i ↔ i ∈ nb j) (V : ι → ℝ) (hV : ∀ i, 0 < V i)
    (c s : ι → ι → Fin D → ℝ) (hs : ∀ i j d, s j i d = s i j d)
    (hc0 : ∀ i d, ∑ j ∈ nb i, c i j d = 0) (hanti : ∀ i j d, V i * c i j d = -(V j * c j i d))
    (et etp : ι → ℝ) (qq : Fin D → ι → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hloc : ∀ i, etp i ≤ et i + τ * ∑ j ∈ nb i, ∑ d,
      (s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j - qq d i))) :
    ∑ i, V i * etp i ≤ ∑ i, V i * et i := by
  have hbal := global_entropy_balance nb hnb V c s hs hc0 et qq
  have hzero : ∀ i j d, (V i * c i j d + V j * c j i d) * (qq d i + qq d j)
      - s i j d * (V i * |c i j d| - V j * |c j i d|) * (et j - et i) = 0 := by
    intro i j d
    have h1 : V i * c i j d + V j * c j i d = 0 := by rw [hanti]; ring
    have h2 : V i * |c i j d| - V j * |c j i d| = 0 := by
      have : |V i * c i j d| = |V j * c j i d| := by rw [hanti, abs_neg]
      rw [abs_mul, abs_mul, abs_of_pos (hV i), abs_of_pos (hV j)] at this
      linarith
    rw [h1, h2]; ring
  simp only [hzero, Finset.sum_const_zero, mul_zero] at hbal
  calc ∑ i, V i * etp i ≤ ∑ i, V i * (et i + τ * ∑ j ∈ nb i, ∑ d,
        (s i j d * |c i j d| * (et j - et i) - c i j d * (qq d j - qq d i))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hloc i) (hV i).le
    _ = ∑ i, V i * et i := by
        simp only [mul_add, Finset.sum_add_distrib]
        have : ∑ i, V i * (τ * ∑ j ∈ nb i, ∑ d, (s i j d * |c i j d| * (et j - et i)
            - c i j d * (qq d j - qq d i))) = τ * 0 := by
          rw [← hbal, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this]; ring

/-- **Corollary 3.7, Runge–Kutta methods with `C > 0`.** If every stage is a convex combination
of `Uⁿ` and forward Euler substeps (Lemma 6.1 of [A]), and a convex functional `Φ` (the total
entropy) does not increase along each substep, then `Φ(Y_k) ≤ Φ(Uⁿ)` for all stages. -/
theorem ssp_convex_functional {X : Type*} [AddCommGroup X] [Module ℝ X] {S : Set X}
    {Φ : X → ℝ} (hΦ : ConvexOn ℝ S Φ) (Y W : ℕ → X) (v : ℕ → ℝ) (α : ℕ → ℕ → ℝ)
    (hv : ∀ k, 0 ≤ v k) (hα : ∀ k j, 0 ≤ α k j) (hsum : ∀ k, v k + ∑ j ∈ range k, α k j = 1)
    (hSO : ∀ k, 1 ≤ k → Y k = v k • Y 0 + ∑ j ∈ range k, α k j • W j)
    (hS : ∀ k, Y k ∈ S ∧ W k ∈ S) (hW : ∀ j, Φ (W j) ≤ Φ (Y j)) :
    ∀ k, Φ (Y k) ≤ Φ (Y 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]
  rw [hSO k hpos]
  classical
  let wt : Option ℕ → ℝ := fun o => o.elim (v k) (fun j => α k j)
  let pt : Option ℕ → X := fun o => o.elim (Y 0) W
  let t : Finset (Option ℕ) := insert none ((range k).map Function.Embedding.some)
  have hw0 : ∀ o ∈ t, 0 ≤ wt o := fun o _ => by cases o <;> simp [wt, hv, hα]
  have hw1 : ∑ o ∈ t, wt o = 1 := by simp [t, wt, Finset.sum_insert, hsum]
  have hmem : ∀ o ∈ t, pt o ∈ S := fun o _ => by cases o <;> simp [pt, hS]
  have h := hΦ.map_sum_le hw0 hw1 hmem
  have e : ∑ o ∈ t, wt o • pt o = v k • Y 0 + ∑ j ∈ range k, α k j • W j := by
    simp [t, wt, pt, Finset.sum_insert]
  rw [e] at h
  refine h.trans ?_
  have e2 : ∑ o ∈ t, wt o • Φ (pt o) = v k * Φ (Y 0) + ∑ j ∈ range k, α k j * Φ (W j) := by
    simp [t, wt, pt, Finset.sum_insert]
  rw [e2]
  calc v k * Φ (Y 0) + ∑ j ∈ range k, α k j * Φ (W j)
      ≤ v k * Φ (Y 0) + ∑ j ∈ range k, α k j * Φ (Y 0) := by
        gcongr with j hj
        · exact hα k j
        · exact (hW j).trans (ih j (Finset.mem_range.1 hj))
    _ = Φ (Y 0) := by rw [← Finset.sum_mul, ← add_mul, hsum, one_mul]

end Entropy

end Meshfree.Stability
