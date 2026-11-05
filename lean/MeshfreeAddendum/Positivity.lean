import MeshfreeAddendum.Scheme
import Mathlib.Algebra.BigOperators.Field

/-!
# The first-order scheme and positivity (Section 5 of the addendum)

* Euler equations: `Euler.flux`, `Euler.Adm`, `Euler.convex_Adm` (convexity of the
  admissible set, stated in Section 2.1) and **Lemma 5.1** `Euler.lf_state_admissible`.
* **Proposition 5.2** `first_order_update_admissible` (abstract convex set and fluxes).
* **Corollary 5.3** `aligned_update_admissible` (aligned orientation, derivative weights
  of any degree) and the scalar local-extremum-diminishing statement `scalar_led`.
* EPD rules and **Proposition 5.6** (fallback): `epdOrder`, `fallback_orders`,
  `fallback_all_order_one`, `epd0_not_fallback`, `truncRecon_one`.
* **Proposition 5.7** `local_admissibility_order_one` (interface orders as a hypothesis) and
  `local_admissibility_order_one_epd` (orders given by the EPD rule on the neighbour graph).
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree

/-! ### Euler equations -/

namespace Euler

variable {D : ℕ}

/-- Conservative state `(ρ, ρu, E)`. -/
abbrev State (D : ℕ) := ℝ × (Fin D → ℝ) × ℝ

def rho (U : State D) : ℝ := U.1
def mom (U : State D) : Fin D → ℝ := U.2.1
def ener (U : State D) : ℝ := U.2.2

/-- Twice the kinetic energy times density: `|m|²`. -/
def msq (U : State D) : ℝ := ∑ i, mom U i ^ 2

/-- Pressure `p = (γ-1)(E - |m|²/(2ρ))`. -/
noncomputable def pres (γ : ℝ) (U : State D) : ℝ := (γ - 1) * (ener U - msq U / (2 * rho U))

/-- Admissible set `{ρ > 0, p > 0}`. -/
def Adm (γ : ℝ) : Set (State D) := {U | 0 < rho U ∧ 0 < pres γ U}

/-- Euler flux in direction `d`, eq. `eq:euler`. -/
noncomputable def flux (γ : ℝ) (d : Fin D) (U : State D) : State D :=
  (mom U d, fun i => mom U d * mom U i / rho U + (if i = d then pres γ U else 0),
    mom U d / rho U * (ener U + pres γ U))

/-- Wave speed bound `λ_d = |u_d| + c`, `c = √(γp/ρ)`. -/
noncomputable def lam (γ : ℝ) (d : Fin D) (U : State D) : ℝ :=
  |mom U d / rho U| + Real.sqrt (γ * pres γ U / rho U)

theorem lam_pos {γ : ℝ} (hγ : 1 < γ) {U : State D} (hU : U ∈ Adm γ) (d : Fin D) :
    0 < lam γ d U := by
  have h1 : 0 < γ * pres γ U / rho U := div_pos (mul_pos (by linarith) hU.2) hU.1
  exact add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.sqrt_pos.2 h1)

theorem quot_ineq {a b x y r1 r2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : 0 < r1) (h2 : 0 < r2)
    (hr : 0 < a * r1 + b * r2) :
    (a * x + b * y) ^ 2 / (a * r1 + b * r2) ≤ a * (x ^ 2 / r1) + b * (y ^ 2 / r2) := by
  have key : a * (x ^ 2 / r1) + b * (y ^ 2 / r2) - (a * x + b * y) ^ 2 / (a * r1 + b * r2)
      = a * b * (x * r2 - y * r1) ^ 2 / (r1 * r2 * (a * r1 + b * r2)) := by
    field_simp; ring
  have : 0 ≤ a * b * (x * r2 - y * r1) ^ 2 / (r1 * r2 * (a * r1 + b * r2)) := by positivity
  linarith

/-- The admissible set of the Euler equations is convex (Section 2.1). -/
theorem convex_Adm {γ : ℝ} (hγ : 1 < γ) : Convex ℝ (Adm (D := D) γ) := by
  intro U hU V hV a b ha hb hab
  have hρU := hU.1; have hρV := hV.1
  have hρ : 0 < a * rho U + b * rho V := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simpa using hρV
    · nlinarith [mul_pos h hρU, mul_nonneg hb hρV.le]
  have heU : 0 < ener U - msq U / (2 * rho U) := by
    have := hU.2; unfold pres at this; nlinarith
  have heV : 0 < ener V - msq V / (2 * rho V) := by
    have := hV.2; unfold pres at this; nlinarith
  have hcomb_rho : rho (a • U + b • V) = a * rho U + b * rho V := by
    simp [rho]
  have hcomb_mom : ∀ i, mom (a • U + b • V) i = a * mom U i + b * mom V i := by
    intro i; simp [mom]
  have hcomb_ener : ener (a • U + b • V) = a * ener U + b * ener V := by
    simp [ener]
  refine ⟨by rw [hcomb_rho]; exact hρ, ?_⟩
  unfold pres
  apply mul_pos (by linarith)
  rw [hcomb_rho, hcomb_ener]
  have hmsq : msq (a • U + b • V) / (2 * (a * rho U + b * rho V))
      ≤ a * (msq U / (2 * rho U)) + b * (msq V / (2 * rho V)) := by
    simp only [msq, hcomb_mom, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := quot_ineq (x := mom U i) (y := mom V i) ha hb (by linarith : 0 < 2 * rho U)
      (by linarith : 0 < 2 * rho V) (by linarith : 0 < a * (2 * rho U) + b * (2 * rho V))
    have e1 : a * (2 * rho U) + b * (2 * rho V) = 2 * (a * rho U + b * rho V) := by ring
    rw [e1] at this
    exact this
  have hpos : 0 < a * (ener U - msq U / (2 * rho U)) + b * (ener V - msq V / (2 * rho V)) := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simpa using heV
    · nlinarith [mul_pos h heU, mul_nonneg hb heV.le]
  nlinarith

theorem sum_sq_sub_single (m : Fin D → ℝ) (θ a : ℝ) (d : Fin D) :
    ∑ i, (θ * m i - (if i = d then a else 0)) ^ 2 = θ ^ 2 * ∑ i, m i ^ 2 - 2 * θ * a * m d + a ^ 2 := by
  have : ∀ i, (θ * m i - (if i = d then a else 0)) ^ 2
      = θ ^ 2 * m i ^ 2 + ((if i = d then (- 2 * θ * a * m d + a ^ 2) else 0)) := by
    intro i
    by_cases h : i = d
    · subst h; simp; ring
    · simp [h]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true,
    ← Finset.mul_sum]
  ring

/-- **Lemma 5.1** (cf. Perthame–Shu, Zhang–Shu). For an admissible Euler state,
`σ = ±1` and `s ≥ |u_d| + c`, the state `U - σ F_d(U)/s` is admissible. -/
theorem lf_state_admissible {γ : ℝ} (hγ : 1 < γ) {U : State D} (hU : U ∈ Adm γ)
    (d : Fin D) {σ s : ℝ} (hσ : σ = 1 ∨ σ = -1) (hs : lam γ d U ≤ s) :
    U - (σ / s) • flux γ d U ∈ Adm γ := by
  obtain ⟨hρ, hp⟩ := hU
  set ρ := rho U
  set p := pres γ U
  set ud := mom U d / ρ
  set c := Real.sqrt (γ * p / ρ)
  have hc2 : c ^ 2 = γ * p / ρ := Real.sq_sqrt (div_pos (mul_pos (by linarith) hp) hρ).le
  have hc : 0 < c := Real.sqrt_pos.2 (div_pos (mul_pos (by linarith) hp) hρ)
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσu : σ * ud ≤ |ud| := by
    rcases hσ with h | h <;> rw [h]
    · simpa using le_abs_self ud
    · simpa using neg_le_abs ud
  have hs' : |ud| + c ≤ s := hs
  have hspos : 0 < s := by linarith [abs_nonneg ud]
  set θ := 1 - σ * ud / s
  have hθs : θ * s = s - σ * ud := by simp only [θ]; field_simp
  have hθs_ge : c ≤ θ * s := by rw [hθs]; linarith
  have hθ : 0 < θ := by
    have : 0 < θ * s := lt_of_lt_of_le hc hθs_ge
    exact pos_of_mul_pos_left this hspos.le
  have hmd : mom U d = ud * ρ := by simp only [ud]; field_simp
  -- components of `W`
  have hρW : rho (U - (σ / s) • flux γ d U) = θ * ρ := by
    show ρ - σ / s * mom U d = θ * ρ
    rw [hmd]; simp only [θ]; ring
  have hmW : ∀ i, mom (U - (σ / s) • flux γ d U) i
      = θ * mom U i - (if i = d then σ / s * p else 0) := by
    intro i
    show mom U i - σ / s * (mom U d * mom U i / ρ + (if i = d then p else 0))
      = θ * mom U i - (if i = d then σ / s * p else 0)
    rw [hmd]
    by_cases h : i = d
    · simp only [h, ite_true]; simp only [θ]; field_simp; ring
    · simp only [h, ite_false]; simp only [θ]; field_simp; ring
  have hEW : ener (U - (σ / s) • flux γ d U) = θ * ener U - σ * ud * p / s := by
    show ener U - σ / s * (mom U d / ρ * (ener U + p)) = θ * ener U - σ * ud * p / s
    simp only [θ]
    have : mom U d / ρ = ud := rfl
    rw [this]; ring
  have hmsqW : msq (U - (σ / s) • flux γ d U)
      = θ ^ 2 * msq U - 2 * θ * (σ / s * p) * mom U d + (σ / s * p) ^ 2 := by
    simp only [msq, hmW]
    exact sum_sq_sub_single _ θ _ d
  have hener : ener U = p / (γ - 1) + msq U / (2 * ρ) := by
    have hp' : p = (γ - 1) * (ener U - msq U / (2 * ρ)) := rfl
    have hγ1 : γ - 1 ≠ 0 := by linarith
    rw [hp']; field_simp; ring
  refine ⟨by rw [hρW]; exact mul_pos hθ hρ, ?_⟩
  unfold pres
  apply mul_pos (by linarith)
  rw [hρW, hEW, hmsqW]
  have key : θ * ener U - σ * ud * p / s
      - (θ ^ 2 * msq U - 2 * θ * (σ / s * p) * mom U d + (σ / s * p) ^ 2) / (2 * (θ * ρ))
      = θ * p / (γ - 1) - p ^ 2 / (2 * θ * ρ * s ^ 2) := by
    rw [hener, hmd]
    have h1 : (σ / s * p) ^ 2 = p ^ 2 / s ^ 2 := by
      rw [div_mul_eq_mul_div, div_pow, mul_pow, hσ2, one_mul]
    rw [h1]
    field_simp
    ring
  rw [key]
  -- `θ p/(γ-1) > p²/(2θρs²)` because `(θ s)² ≥ c² = γ p/ρ > (γ-1) p/(2ρ)`
  have hθs2 : γ * p / ρ ≤ (θ * s) ^ 2 := by
    rw [← hc2]; exact pow_le_pow_left₀ hc.le hθs_ge 2
  have hθs2' : γ * p ≤ ρ * (θ * s) ^ 2 := by
    rw [div_le_iff₀ hρ] at hθs2; linarith
  rw [sub_pos, div_lt_div_iff₀ (by positivity) (by linarith)]
  nlinarith [mul_pos hp hθ, mul_pos (mul_pos hp hθ) hρ]

end Euler

/-! ### Proposition 5.2 -/

section FirstOrder

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {D : ℕ} {J : Type*} [Fintype J]

/-- The scheme operator `eq:scheme` at a particle with states `Ui` and interface states
`Uij`, `Uji`. -/
noncomputable def schemeOp (F : Fin D → E → E) (c σ s : J → Fin D → ℝ) (Ui : E)
    (Uij Uji : J → E) : E :=
  (-(2 : ℝ)) • ∑ j, ∑ d, c j d • (rusanov (F d) (s j d) (σ j d) (Uij j) (Uji j) - F d Ui)

/-- The flux hypothesis of Proposition 5.2: `U - σ F_d(U)/s ∈ G` for admissible `U`,
`σ = ±1` and `s ≥ λ_d(U)`, `s > 0`. -/
def LFHyp (G : Set E) (F : Fin D → E → E) (lam : Fin D → E → ℝ) : Prop :=
  ∀ U ∈ G, ∀ d σ s, (σ = 1 ∨ σ = -1) → lam d U ≤ s → 0 < s → U - (σ / s) • F d U ∈ G

theorem Euler.lfHyp {D : ℕ} {γ : ℝ} (hγ : 1 < γ) :
    LFHyp (Euler.Adm (D := D) γ) (Euler.flux γ) (Euler.lam γ) :=
  fun _U hU d _σ _s hσ hs _ => Euler.lf_state_admissible hγ hU d hσ hs

theorem term_identity (F : E → E) (c σ s : ℝ) (Ui Uj : E) (hs : 0 < s)
    (hσ : σ = -1 ∨ σ = 0 ∨ σ = 1) (hb : σ * c = |c|) :
    (-(2 : ℝ)) • (c • (rusanov F s σ Ui Uj - F Ui))
      = (s * |c|) • (Uj - (σ / s) • F Uj) - (s * |c|) • Ui + c • F Ui := by
  have hc : c = σ * |c| := by
    rcases hσ with h | h | h <;> rw [h] at hb ⊢
    · linarith
    · simp at hb; rw [abs_eq_zero.1 hb.symm]; simp
    · linarith
  have h1 : s * |c| * (σ / s) = c := by rw [hc]; field_simp; rw [← hc]; ring_nf; rw [← hc]
  have h2 : c * s * σ = s * |c| := by rw [← hb]; ring
  have lhs : (-(2 : ℝ)) • (c • (rusanov F s σ Ui Uj - F Ui))
      = c • F Ui - c • F Uj + (c * s * σ) • (Uj - Ui) := by
    unfold rusanov; module
  rw [lhs, h2]
  rw [show (s * |c|) • (Uj - (σ / s) • F Uj) = (s * |c|) • Uj - c • F Uj by
    rw [smul_sub, smul_smul, h1]]
  module

/-- **Proposition 5.2 (positivity of the first-order update).** -/
theorem first_order_update_admissible {G : Set E} (hG : Convex ℝ G) {F : Fin D → E → E}
    {lam : Fin D → E → ℝ} (hLF : LFHyp G F lam) (c σ s : J → Fin D → ℝ) (Ui : E)
    (Uj : J → E)
    (ha : ∀ d, ∑ j, c j d = 0)
    (hb : ∀ j d, σ j d * c j d = |c j d|) (hσ : ∀ j d, σ j d = -1 ∨ σ j d = 0 ∨ σ j d = 1)
    (hs : ∀ j d, lam d (Uj j) ≤ s j d) (hspos : ∀ j d, 0 < s j d)
    (hUi : Ui ∈ G) (hUj : ∀ j, Uj j ∈ G) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : τ * ∑ j, ∑ d, s j d * |c j d| ≤ 1) :
    Ui + τ • schemeOp F c σ s Ui (fun _ => Ui) Uj ∈ G := by
  set W : J × Fin D → E := fun p => Uj p.1 - (σ p.1 p.2 / s p.1 p.2) • F p.2 (Uj p.1)
  set β : J × Fin D → ℝ := fun p => τ * (s p.1 p.2 * |c p.1 p.2|)
  have hW : ∀ p, W p ∈ G := by
    intro ⟨j, d⟩
    rcases hσ j d with h | h | h
    · exact hLF _ (hUj j) d _ _ (Or.inr h) (hs j d) (hspos j d)
    · simp only [W, h, zero_div, zero_smul, sub_zero]; exact hUj j
    · exact hLF _ (hUj j) d _ _ (Or.inl h) (hs j d) (hspos j d)
  have hsum : ∑ p, β p = τ * ∑ j, ∑ d, s j d * |c j d| := by
    simp only [β, ← Finset.mul_sum, Fintype.sum_prod_type]
  -- the update as a convex combination
  have hupd : Ui + τ • schemeOp F c σ s Ui (fun _ => Ui) Uj
      = (1 - ∑ p, β p) • Ui + ∑ p, β p • W p := by
    have hterm : ∀ j d, (-(2 : ℝ)) • (c j d • (rusanov (F d) (s j d) (σ j d) Ui (Uj j) - F d Ui))
        = (s j d * |c j d|) • W (j, d) - (s j d * |c j d|) • Ui + c j d • F d Ui :=
      fun j d => term_identity (F d) _ _ _ Ui (Uj j) (hspos j d) (hσ j d) (hb j d)
    have hzero : ∑ j, ∑ d, c j d • F d Ui = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [← Finset.sum_smul, ha d, zero_smul]
    have e1 : schemeOp F c σ s Ui (fun _ => Ui) Uj = ∑ j, ∑ d,
        ((s j d * |c j d|) • W (j, d) - (s j d * |c j d|) • Ui + c j d • F d Ui) := by
      unfold schemeOp
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => hterm j d
    have e2 : (∑ j, ∑ d,
        ((s j d * |c j d|) • W (j, d) - (s j d * |c j d|) • Ui + c j d • F d Ui))
        = ∑ j, ∑ d, (s j d * |c j d|) • W (j, d) - (∑ j, ∑ d, s j d * |c j d|) • Ui := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hzero, add_zero,
        Finset.sum_smul]
    rw [e1, e2, hsum, Fintype.sum_prod_type]
    simp only [β, smul_sub, Finset.smul_sum, smul_smul, sub_smul, one_smul]
    abel
  rw [hupd]
  -- convex combination over `Option (J × Fin D)`
  have hβ : ∀ p, 0 ≤ β p := fun p => mul_nonneg hτ (mul_nonneg (hspos _ _).le (abs_nonneg _))
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

/-- **Corollary 5.3 (aligned orientation).** With `σ = sign(c)` (the signs of the
weights actually used) condition (b) holds by construction; with zero row sums the
first-order update is admissible. The weights may be of any degree. -/
theorem aligned_update_admissible {G : Set E} (hG : Convex ℝ G) {F : Fin D → E → E}
    {lam : Fin D → E → ℝ} (hLF : LFHyp G F lam) (c s : J → Fin D → ℝ) (Ui : E) (Uj : J → E)
    (ha : ∀ d, ∑ j, c j d = 0)
    (hs : ∀ j d, lam d (Uj j) ≤ s j d) (hspos : ∀ j d, 0 < s j d)
    (hUi : Ui ∈ G) (hUj : ∀ j, Uj j ∈ G) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : τ * ∑ j, ∑ d, s j d * |c j d| ≤ 1) :
    Ui + τ • schemeOp F c (fun j d => Real.sign (c j d)) s Ui (fun _ => Ui) Uj ∈ G :=
  first_order_update_admissible hG hLF c _ s Ui Uj ha
    (fun j d => ConsData.sign_mul_self _) (fun j d => Real.sign_apply_eq _)
    hs hspos hUi hUj hτ hcfl

/-- **Corollary 5.3, scalar case (local extremum diminishing).** For a scalar law,
write `F_d(U_j) - F_d(U_i) = a_{ij,d}(U_j - U_i)` with `|a| ≤ s`. With zero-sum weights
and aligned orientation the update lies between the local minimum and maximum if
`2τ ∑ s|c| ≤ 1`. -/
theorem scalar_led (F : Fin D → ℝ → ℝ) (c s a : J → Fin D → ℝ) (Ui : ℝ) (Uj : J → ℝ)
    (ha0 : ∀ d, ∑ j, c j d = 0)
    (hquot : ∀ j d, F d (Uj j) - F d Ui = a j d * (Uj j - Ui))
    (has : ∀ j d, |a j d| ≤ s j d) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : 2 * τ * ∑ j, ∑ d, s j d * |c j d| ≤ 1) {lo hi : ℝ}
    (hlo : lo ≤ Ui ∧ ∀ j, lo ≤ Uj j) (hhi : Ui ≤ hi ∧ ∀ j, Uj j ≤ hi) :
    let upd := Ui + τ * schemeOp F c (fun j d => Real.sign (c j d)) s Ui (fun _ => Ui) Uj
    lo ≤ upd ∧ upd ≤ hi := by
  intro upd
  set β : J → Fin D → ℝ := fun j d => τ * (s j d * |c j d| - c j d * a j d)
  have hβ0 : ∀ j d, 0 ≤ β j d := by
    intro j d
    have : |c j d * a j d| ≤ s j d * |c j d| := by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (has j d) (abs_nonneg _)
    exact mul_nonneg hτ (by linarith [le_abs_self (c j d * a j d)])
  have hβ1 : ∀ j d, β j d ≤ 2 * τ * (s j d * |c j d|) := by
    intro j d
    have : -(c j d * a j d) ≤ s j d * |c j d| := by
      have h1 := neg_abs_le (c j d * a j d)
      rw [abs_mul, mul_comm (|c j d|)] at h1
      nlinarith [mul_le_mul_of_nonneg_right (has j d) (abs_nonneg (c j d))]
    have := mul_le_mul_of_nonneg_left this hτ
    simp only [β]; nlinarith
  have hsumβ : ∑ j, ∑ d, β j d ≤ 1 := by
    calc ∑ j, ∑ d, β j d ≤ ∑ j, ∑ d, 2 * τ * (s j d * |c j d|) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun d _ => hβ1 j d
      _ = 2 * τ * ∑ j, ∑ d, s j d * |c j d| := by simp only [Finset.mul_sum]
      _ ≤ 1 := hcfl
  have hupd : upd = Ui + ∑ j, ∑ d, β j d * (Uj j - Ui) := by
    simp only [upd, schemeOp, rusanov, smul_eq_mul]
    have hterm : ∀ j d, c j d * ((1 / 2) * (F d Ui + F d (Uj j))
        - (1 / 2) * s j d * Real.sign (c j d) * (Uj j - Ui) - F d Ui)
        = (1 / 2) * (c j d * a j d) * (Uj j - Ui)
          - (1 / 2) * (s j d * |c j d|) * (Uj j - Ui) := by
      intro j d
      have hF : F d (Uj j) = F d Ui + a j d * (Uj j - Ui) := by linarith [hquot j d]
      rw [hF, ← ConsData.sign_mul_self (c j d)]; ring
    simp only [hterm, Finset.mul_sum, β]
    congr 1
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun d _ => by ring
  have hrepr : upd = (1 - ∑ j, ∑ d, β j d) * Ui + ∑ j, ∑ d, β j d * Uj j := by
    rw [hupd]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  constructor
  · rw [hrepr]
    calc lo = (1 - ∑ j, ∑ d, β j d) * lo + ∑ j, ∑ d, β j d * lo := by
          simp only [← Finset.sum_mul]; ring
      _ ≤ _ := by
          gcongr with j _ d _ <;>
            first | exact hlo.1 | exact hβ0 j d | exact hlo.2 j | linarith
  · rw [hrepr]
    calc (1 - ∑ j, ∑ d, β j d) * Ui + ∑ j, ∑ d, β j d * Uj j
        ≤ (1 - ∑ j, ∑ d, β j d) * hi + ∑ j, ∑ d, β j d * hi := by
          gcongr with j _ d _ <;>
            first | exact hhi.1 | exact hβ0 j d | exact hhi.2 j | linarith
      _ = hi := by simp only [← Finset.sum_mul]; ring

end FirstOrder

/-! ### EPD rules and Proposition 5.6 (fallback) -/

section Fallback

/-- The interface rules EPD0, EPD1, EPD2 of `eq:epd`. -/
inductive EPD | zero | one | two
  deriving DecidableEq

variable {P : Type*} [DecidableEq P]

/-- Closed neighbourhood `ν̄(i) = ν(i) ∪ {i}`. -/
def cnb (nb : P → Finset P) (i : P) : Finset P := insert i (nb i)

/-- The interface order `k_{i→j}` under a rule. -/
def epdOrder (nb : P → Finset P) (k : P → ℕ) : EPD → P → P → ℕ
  | .zero, i, _ => k i
  | .one, i, j => min (k i) (k j)
  | .two, i, j => (cnb nb i ∪ cnb nb j).inf' ⟨i, by simp [cnb]⟩ k

theorem epdOrder_le (nb : P → Finset P) (k : P → ℕ) (r : EPD) (i j : P) :
    epdOrder nb k r i j ≤ k i := by
  cases r with
  | zero => exact le_rfl
  | one => exact min_le_left _ _
  | two => exact Finset.inf'_le _ (by simp [cnb])

/-- **Proposition 5.6**, orders: if `k_i = 1` (and all orders are `≥ 1`), then under
EPD1 and EPD2 both interface orders of every edge of `i` are one. -/
theorem fallback_orders (nb : P → Finset P) (k : P → ℕ) (hk : ∀ l, 1 ≤ k l) {i : P}
    (hi : k i = 1) (r : EPD) (hr : r ≠ .zero) (j : P) :
    epdOrder nb k r i j = 1 ∧ epdOrder nb k r j i = 1 := by
  cases r with
  | zero => exact absurd rfl hr
  | one =>
    simp only [epdOrder, hi]
    exact ⟨by have := hk j; omega, by have := hk j; omega⟩
  | two =>
    simp only [epdOrder]
    have h1 : ∀ (S : Finset P) (hS : S.Nonempty), i ∈ S → S.inf' hS k = 1 := by
      intro S hS hiS
      apply le_antisymm
      · rw [← hi]; exact Finset.inf'_le _ hiS
      · exact Finset.le_inf' _ _ fun l _ => hk l
    exact ⟨h1 _ _ (by simp [cnb]), h1 _ _ (by simp [cnb])⟩

/-- **Proposition 5.6**, `K = 1`: all orders are one, so every rule gives order one. -/
theorem fallback_all_order_one (nb : P → Finset P) (k : P → ℕ) (hk : ∀ l, 1 ≤ k l)
    (hK : ∀ l, k l ≤ 1) (r : EPD) (i j : P) : epdOrder nb k r i j = 1 := by
  have := epdOrder_le nb k r i j
  have h1 : 1 ≤ epdOrder nb k r i j := by
    cases r with
    | zero => exact hk i
    | one => exact le_min (hk i) (hk j)
    | two => simp only [epdOrder]; exact Finset.le_inf' _ _ fun l _ => hk l
  have := hK i; omega

/-- **Proposition 5.6**, EPD0: the neighbour's interface order is its own order and
may exceed one. -/
theorem epd0_not_fallback :
    ∃ (k : Fin 2 → ℕ), k 0 = 1 ∧ epdOrder (fun _ => univ) k .zero 1 0 = 2 :=
  ⟨![1, 2], rfl, rfl⟩

variable {D : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The truncated reconstruction `R^{[r]}(y) = U + ∑_{1≤|α|≤r-1} a_α y^α/α!`. -/
noncomputable def truncRecon (U : E) (a : (Fin D → ℕ) → E) (r : ℕ) (y : Pt D) : E :=
  U + ∑ α ∈ misPos D (r - 1), mono α y • a α

theorem misPos_zero : misPos D 0 = ∅ := by
  ext α
  simp only [misPos, mem_erase, mem_mis, Finset.notMem_empty, iff_false, not_and]
  intro hne hdeg
  apply hne
  funext i
  have := le_deg α i
  simp only [Pi.zero_apply]
  omega

/-- `R^{[1]} ≡ U`: order-one interface states are piecewise constant. -/
theorem truncRecon_one (U : E) (a : (Fin D → ℕ) → E) (y : Pt D) : truncRecon U a 1 y = U := by
  simp [truncRecon, misPos_zero]

/-- Under EPD0 with `K ≥ 2` the fallback fails: an order-two neighbour with a non-zero
slope contributes a non-constant interface state (`D = 1`, `U_j = 0`, slope `1`,
`x_{ij} = 1`). -/
theorem epd0_state_not_constant :
    truncRecon (D := 1) (0 : ℝ) (fun α => if α = unit 0 then 1 else 0) 2
      (-(1 / 2 : ℝ) • (fun _ => 1)) ≠ 0 := by
  have h0 : ∀ β : Fin 1 → ℕ, β = (fun _ => β 0) := fun β => funext fun i => by
    fin_cases i; rfl
  have hmis : misPos 1 1 = {unit 0} := by
    ext α
    simp only [misPos, mem_erase, mem_mis, Finset.mem_singleton, deg, Fin.sum_univ_one, ne_eq]
    constructor
    · rintro ⟨hne, hle⟩
      have hα : α 0 ≠ 0 := fun h => hne (by rw [h0 α, h]; rfl)
      rw [h0 α, h0 (unit 0)]
      have : α 0 = 1 := by omega
      simp [unit, this]
    · rintro rfl; simp [unit]
  simp only [truncRecon, Nat.add_one_sub_one, hmis, Finset.sum_singleton, ite_true, mono_unit]
  norm_num

end Fallback

/-! ### Proposition 5.7: local admissibility at order one -/

section Local

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {D : ℕ} {J : Type*} [Fintype J]

/-- Whether an edge is aligned: `min{k_i, k_j} < K` or `K = 1`. -/
def IsAligned (K ki kj : ℕ) : Prop := min ki kj < K ∨ K = 1

instance (K ki kj : ℕ) : Decidable (IsAligned K ki kj) := by unfold IsAligned; infer_instance

/-- Geometric orientation with the implementation's convention `-1` for `x_d = 0`. -/
noncomputable def geomSign (r : ℝ) : ℝ := if r = 0 then -1 else Real.sign r

/-- The orientation of the aligned Rusanov flux at particle `i`. -/
noncomputable def alignedFluxOrientation (K ki : ℕ) (kj : J → ℕ) (c : J → Fin D → ℝ)
    (x : J → Pt D) (j : J) (d : Fin D) : ℝ :=
  if IsAligned K ki (kj j) then Real.sign (c j d) else geomSign (x j d)

/-- **Proposition 5.7 (local admissibility at order one).**

Particle `i` with order `k_i = 1` (orders `≥ 1`, `≤ K`), neighbour orders `kj`,
interface orders `kij`, `kji` given by a rule `r` (EPD1/EPD2, or any rule if `K = 1`;
`hord` says that the interface orders are those of the rule on the neighbour graph,
which via `fallback_orders` / `fallback_all_order_one` makes them one), interface states
from truncated reconstructions, the aligned Rusanov flux with the signs of the weights in
use, unregularized derivative weights of any degree `q ≥ 1` on a `Π_q`-unisolvent
neighbourhood, admissible states on `ν̄(i)` and the CFL condition `eq:cflpos`. -/
theorem local_admissibility_order_one {G : Set E} (hG : Convex ℝ G) {F : Fin D → E → E}
    {lam : Fin D → E → ℝ} (hLF : LFHyp G F lam) (hlam : ∀ d U, U ∈ G → 0 < lam d U)
    (K : ℕ) (ki : ℕ) (kj kij kji : J → ℕ) (hki : ki = 1) (hK : 1 ≤ K)
    (hord : ∀ j, kij j = 1 ∧ kji j = 1)
    {q : ℕ} (hq : 1 ≤ q) {w : J → ℝ} {x : J → Pt D} (hw : ∀ j, 0 < w j)
    (hU : UnisolventAt q x)
    (Yi : E) (Yj : J → E) (ai : (Fin D → ℕ) → E) (aj : J → (Fin D → ℕ) → E)
    (hYi : Yi ∈ G) (hYj : ∀ j, Yj j ∈ G) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : τ * ∑ j, ∑ d, max (lam d Yi) (lam d (Yj j)) * |divWeight q hq w x d j| ≤ 1) :
    let c := fun j d => divWeight q hq w x d j
    let Uij := fun j => truncRecon Yi ai (kij j) ((1 / 2 : ℝ) • x j)
    let Uji := fun j => truncRecon (Yj j) (aj j) (kji j) (-(1 / 2 : ℝ) • x j)
    Yi + τ • schemeOp F c (alignedFluxOrientation K ki kj c x)
      (fun j d => max (lam d Yi) (lam d (Yj j))) Yi Uij Uji ∈ G := by
  intro c Uij Uji
  -- fallback: piecewise constant states
  have hUij : Uij = fun _ => Yi := by
    funext j; simp only [Uij, (hord j).1, truncRecon_one]
  have hUji : Uji = Yj := by
    funext j; simp only [Uji, (hord j).2, truncRecon_one]
  -- all edges of `i` are aligned
  have hal : alignedFluxOrientation K ki kj c x = fun j d => Real.sign (c j d) := by
    funext j d
    have : IsAligned K ki (kj j) := by
      unfold IsAligned
      rcases Nat.lt_or_ge 1 K with h | h
      · left; rw [hki]; exact lt_of_le_of_lt (min_le_left _ _) h
      · right; omega
    simp [alignedFluxOrientation, this]
  rw [hUij, hUji, hal]
  exact aligned_update_admissible hG hLF c _ Yi Yj
    (fun d => divWeight_sum_eq_zero hq hw hU d)
    (fun j d => le_max_right _ _) (fun j d => lt_max_of_lt_left (hlam d Yi hYi))
    hYi hYj hτ hcfl

/-- **Proposition 5.7, composed with the EPD rule** (no free interface orders).

The interface orders of every edge of `i` are those of the rule `r` on the neighbour
graph `nb` with particle orders `k` (all `≥ 1`); `ι` maps the local neighbour indices to
particles. The rule is EPD1 or EPD2, or any rule if all orders are `≤ 1` (the case
`K = 1`). Then `local_admissibility_order_one` applies with `hord` discharged by
`fallback_orders` / `fallback_all_order_one`. -/
theorem local_admissibility_order_one_epd {G : Set E} (hG : Convex ℝ G) {F : Fin D → E → E}
    {lam : Fin D → E → ℝ} (hLF : LFHyp G F lam) (hlam : ∀ d U, U ∈ G → 0 < lam d U)
    {P : Type*} [DecidableEq P] (nb : P → Finset P) (k : P → ℕ) (hk : ∀ l, 1 ≤ k l)
    (r : EPD) (i : P) (hi : k i = 1) (hrule : r ≠ .zero ∨ ∀ l, k l ≤ 1)
    (K : ℕ) (hK : 1 ≤ K) (ι : J → P)
    {q : ℕ} (hq : 1 ≤ q) {w : J → ℝ} {x : J → Pt D} (hw : ∀ j, 0 < w j)
    (hU : UnisolventAt q x)
    (Yi : E) (Yj : J → E) (ai : (Fin D → ℕ) → E) (aj : J → (Fin D → ℕ) → E)
    (hYi : Yi ∈ G) (hYj : ∀ j, Yj j ∈ G) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : τ * ∑ j, ∑ d, max (lam d Yi) (lam d (Yj j)) * |divWeight q hq w x d j| ≤ 1) :
    let c := fun j d => divWeight q hq w x d j
    let Uij := fun j => truncRecon Yi ai (epdOrder nb k r i (ι j)) ((1 / 2 : ℝ) • x j)
    let Uji := fun j => truncRecon (Yj j) (aj j) (epdOrder nb k r (ι j) i) (-(1 / 2 : ℝ) • x j)
    Yi + τ • schemeOp F c (alignedFluxOrientation K (k i) (fun j => k (ι j)) c x)
      (fun j d => max (lam d Yi) (lam d (Yj j))) Yi Uij Uji ∈ G := by
  have hord : ∀ j, epdOrder nb k r i (ι j) = 1 ∧ epdOrder nb k r (ι j) i = 1 := by
    intro j
    rcases hrule with hr | hK1
    · exact fallback_orders nb k hk hi r hr (ι j)
    · exact ⟨fallback_all_order_one nb k hk hK1 r i (ι j),
        fallback_all_order_one nb k hk hK1 r (ι j) i⟩
  exact local_admissibility_order_one hG hLF hlam K (k i) (fun j => k (ι j))
    (fun j => epdOrder nb k r i (ι j)) (fun j => epdOrder nb k r (ι j) i) hi hK hord hq hw hU
    Yi Yj ai aj hYi hYj hτ hcfl

end Local

end Meshfree
