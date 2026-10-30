import MeshfreeStability.Bloch

/-!
# Section 7: smoothly deformed lattices

The grid is a finite abelian group `G` (the index torus `ℤ_n^D`), the stencil a finite symmetric
set `F ⊆ G` of offsets, and a difference operator is `(PU)_i = ∑_{l∈F} B_l(i) U_{i+l}`
(`dop`).

* Step 2 of the proof of **Theorem 7.3** (central part): `dop_V_symmetrize`,
  `dop_weighted_bound`.
* Step 3 (dissipative part, transfer of the sharp Gårding inequality from `ℓ²` to the
  volume norm): `dop_bound`, `gaarding_transfer`.
* Step 4: `deformed_energy`, `deformed_stability`.

**Hypotheses.** (a) Step 1 of the proof (the coefficients of `hL_h` are `C²` functions of the
particle position with the frozen coefficients as `h → 0`) enters through its consequences: the
`O(h)` bound on the symmetrized central coefficients and the `O(h)` bound of the volume-ratio
correction; (b) the **Lax–Nirenberg (sharp Gårding) inequality** for the frozen dissipative
operator is a hypothesis (it is cited, not proved, in the note); (c) (D4) enters only through (b).
Corollary 7.4 is the composition of `k2_lattice_1d_symbol` (frozen stability) with this theorem;
the sign argument for the aligned orientation in its proof is not formalized.
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Difference operator `(PU)_i = ∑_{l∈F} B_l(i) U_{i+l}`. -/
def dop (F : Finset G) (B : G → G → ℝ) (U : G → ℝ) : G → ℝ := fun i => ∑ l ∈ F, B l i * U (i + l)

/-- Translation invariance of sums over the group. -/
theorem sum_shift (f : G → ℝ) (l : G) : ∑ i, f (i + l) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addRight l) _ _ (fun _ => rfl)

/-- **Unweighted bound.** `|∑_i u_i (Pu)_i| ≤ |F| ε |u|²` if all coefficients are `≤ ε`. -/
theorem dop_bound (F : Finset G) (B : G → G → ℝ) {ε : ℝ} (hB : ∀ l ∈ F, ∀ i, |B l i| ≤ ε)
    (u : G → ℝ) : |∑ i, u i * dop F B u i| ≤ F.card * ε * esq u := by
  simp only [dop, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [show (F.card : ℝ) * ε * esq u = ∑ l ∈ F, ε * esq u by rw [Finset.sum_const, nsmul_eq_mul]; ring]
  refine Finset.sum_le_sum fun l hl => ?_
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hB l hl (0 : G))
  calc ∑ i, |u i * (B l i * u (i + l))| ≤ ∑ i, ε * ((u i ^ 2 + u (i + l) ^ 2) / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_mul]
        have h1 : |u i| * |u (i + l)| ≤ (u i ^ 2 + u (i + l) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|u i| - |u (i + l)|), sq_abs (u i), sq_abs (u (i + l))]
        calc |u i| * (|B l i| * |u (i + l)|) = |B l i| * (|u i| * |u (i + l)|) := by ring
          _ ≤ ε * ((u i ^ 2 + u (i + l) ^ 2) / 2) :=
            mul_le_mul (hB l hl i) h1 (by positivity) hε
    _ = ε * esq u := by
        rw [← Finset.mul_sum]; congr 1
        have hs : ∑ i, u (i + l) ^ 2 = ∑ i, u i ^ 2 := sum_shift (fun i => u i ^ 2) l
        rw [← Finset.sum_div, Finset.sum_add_distrib, hs]; simp only [esq]; ring

/-- **The `V`-adjoint (Step 2).** For a symmetric stencil (`l ∈ F ⇒ -l ∈ F`),
`∑_i V_i U_i (PU)_i = ∑_i V_i U_i ∑_{l∈F} (V_{i+l}/V_i) B_{-l}(i+l) U_{i+l}`; hence twice the
energy is given by the symmetrized coefficients `B_l(i) + (V_{i+l}/V_i) B_{-l}(i+l)`. -/
theorem dop_V_symmetrize (F : Finset G) (hF : ∀ l ∈ F, -l ∈ F) (B : G → G → ℝ) (V : G → ℝ)
    (hV : ∀ i, V i ≠ 0) (U : G → ℝ) :
    2 * ∑ i, V i * U i * dop F B U i
      = ∑ i, V i * U i * ∑ l ∈ F, (B l i + V (i + l) / V i * B (-l) (i + l)) * U (i + l) := by
  have hrefl : ∑ i, V i * U i * dop F B U i
      = ∑ i, V i * U i * ∑ l ∈ F, V (i + l) / V i * B (-l) (i + l) * U (i + l) := by
    simp only [dop, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := univ)]
    -- reindex `l ↦ -l` and `i ↦ i + l`
    have hneg : ∀ f : G → ℝ, ∑ l ∈ F, f l = ∑ l ∈ F, f (-l) := by
      intro f
      exact Finset.sum_nbij' (fun l => -l) (fun l => -l) (fun l hl => hF l hl)
        (fun l hl => hF l hl) (fun l _ => neg_neg l) (fun l _ => neg_neg l) (fun l _ => by simp)
    rw [hneg]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← sum_shift _ l]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [add_neg_cancel_right]
    field_simp [hV i]
  rw [two_mul]; nth_rewrite 2 [hrefl]
  simp only [dop, ← Finset.sum_add_distrib, ← mul_add, add_mul]

/-- **Step 2, the bound.** If the symmetrized coefficients are bounded by `ε` and neighbouring
volumes are comparable (`V_{i+l} ≥ V_i/ρ`… written `V_i ≤ ρ V_{i+l}`), then
`2 |⟨U, PU⟩_V| ≤ |F| ε (1+ρ)/2 · ‖U‖²_V`. -/
theorem dop_weighted_bound (F : Finset G) (hF : ∀ l ∈ F, -l ∈ F) (B : G → G → ℝ) (V : G → ℝ)
    (hV : ∀ i, 0 < V i) {ε ρ : ℝ} (hρ : ∀ l ∈ F, ∀ i, V i ≤ ρ * V (i + l))
    (hsym : ∀ l ∈ F, ∀ i, |B l i + V (i + l) / V i * B (-l) (i + l)| ≤ ε) (U : G → ℝ) :
    2 * ∑ i, V i * U i * dop F B U i ≤ F.card * ε * (1 + ρ) / 2 * wip V U U := by
  rw [dop_V_symmetrize F hF B V (fun i => (hV i).ne') U]
  set e : G → G → ℝ := fun l i => B l i + V (i + l) / V i * B (-l) (i + l)
  have hε : ∀ l ∈ F, 0 ≤ ε := fun l hl => le_trans (abs_nonneg _) (hsym l hl 0)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [show (F.card : ℝ) * ε * (1 + ρ) / 2 * wip V U U
      = ∑ l ∈ F, ε * (1 + ρ) / 2 * wip V U U by rw [Finset.sum_const, nsmul_eq_mul]; ring]
  refine Finset.sum_le_sum fun l hl => ?_
  calc ∑ i, V i * U i * (e l i * U (i + l))
      ≤ ∑ i, ε * (V i * U i ^ 2 + V i * U (i + l) ^ 2) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : |U i * U (i + l)| ≤ (U i ^ 2 + U (i + l) ^ 2) / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|U i| - |U (i + l)|), sq_abs (U i), sq_abs (U (i + l))]
        have h2 := hsym l hl i
        have hVi := hV i
        calc V i * U i * (e l i * U (i + l)) ≤ |V i * U i * (e l i * U (i + l))| := le_abs_self _
          _ = V i * |e l i| * |U i * U (i + l)| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hVi]; ring
          _ ≤ V i * ε * ((U i ^ 2 + U (i + l) ^ 2) / 2) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h2 hVi.le) h1 (abs_nonneg _)
                (mul_nonneg hVi.le (hε l hl))
          _ = _ := by ring
    _ ≤ ∑ i, ε * (V i * U i ^ 2 + ρ * (V (i + l) * U (i + l) ^ 2)) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h0 := mul_le_mul_of_nonneg_right (hρ l hl i) (sq_nonneg (U (i + l)))
        have h3 : ε * (V i * U (i + l) ^ 2) ≤ ε * (ρ * (V (i + l) * U (i + l) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (hε l hl)
        linarith
    _ = ε * (1 + ρ) / 2 * wip V U U := by
        simp only [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
        rw [sum_shift (fun i => V i * U i ^ 2) l]
        simp only [wip, esq]
        rw [show ∑ i, V i * U i * U i = ∑ i, V i * (U i * U i) from
          Finset.sum_congr rfl fun i _ => by ring]
        ring

/-- **Step 3, transfer of the sharp Gårding inequality.** If the frozen dissipative operator
satisfies `∑_i u_i (P₀u)_i ≤ K h |u|²` in `ℓ²` (Lax–Nirenberg, hypothesis `hLN`) and the
volume-ratio correction `(√(V_i/V_{i+l}) - 1) β_l(i)` is bounded by `C₃ h`, then
`⟨U, P₀U⟩_V ≤ (K + |F| C₃) h ‖U‖²_V`. -/
theorem gaarding_transfer (F : Finset G) (β : G → G → ℝ) (V : G → ℝ) (hV : ∀ i, 0 < V i)
    {K C₃ h : ℝ}
    (hLN : ∀ u : G → ℝ, ∑ i, u i * dop F β u i ≤ K * h * esq u)
    (hratio : ∀ l ∈ F, ∀ i, |(Real.sqrt (V i / V (i + l)) - 1) * β l i| ≤ C₃ * h) (U : G → ℝ) :
    ∑ i, V i * U i * dop F β U i ≤ (K + F.card * C₃) * h * wip V U U := by
  set u : G → ℝ := fun i => Real.sqrt (V i) * U i
  have hu : esq u = wip V U U := by
    simp only [esq, wip, u]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mul_pow, Real.sq_sqrt (hV i).le]; ring
  set β' : G → G → ℝ := fun l i => (Real.sqrt (V i / V (i + l)) - 1) * β l i
  have hsplit : ∑ i, V i * U i * dop F β U i
      = ∑ i, u i * dop F β u i + ∑ i, u i * dop F β' u i := by
    simp only [dop, u, β', Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    have h1 : Real.sqrt (V i / V (i + l)) * Real.sqrt (V (i + l)) = Real.sqrt (V i) := by
      rw [← Real.sqrt_mul (div_nonneg (hV i).le (hV _).le), div_mul_cancel₀ _ (hV _).ne']
    have h2 : Real.sqrt (V i) * Real.sqrt (V i) = V i := Real.mul_self_sqrt (hV i).le
    calc V i * U i * (β l i * U (i + l))
        = Real.sqrt (V i) * Real.sqrt (V i) * U i * (β l i * U (i + l)) := by rw [h2]
      _ = Real.sqrt (V i) * U i * (β l i * (Real.sqrt (V (i + l)) * U (i + l)))
          + Real.sqrt (V i) * U i * ((Real.sqrt (V i / V (i + l)) - 1) * β l i *
            (Real.sqrt (V (i + l)) * U (i + l))) := by
          rw [← h1]; ring
  rw [hsplit]
  have h1 := hLN u
  have h2 := le_trans (le_abs_self _) (dop_bound F β' hratio u)
  rw [hu] at h1 h2
  nlinarith

/-- **Theorem 7.3, Step 4: the energy inequality.** `hL_h = P^c + P^d₀ + h P₁` with
* (Step 2) symmetrized central coefficients `≤ C₁ h`, comparable neighbouring volumes;
* (Step 3) Lax–Nirenberg for `P^d₀` and the volume-ratio correction `≤ C₃ h`;
* `⟨U, P₁U⟩_V ≤ C₂ ‖U‖²_V`.
Then `⟨U, L_h U⟩_V ≤ ω ‖U‖²_V` with `ω` independent of `h`. -/
theorem deformed_energy (F : Finset G) (hF : ∀ l ∈ F, -l ∈ F) (Bc β : G → G → ℝ)
    (P₁ : (G → ℝ) → G → ℝ) (V : G → ℝ) (hV : ∀ i, 0 < V i) {h ρ C₁ C₂ C₃ K : ℝ} (hh : 0 < h)
    (hρ : ∀ l ∈ F, ∀ i, V i ≤ ρ * V (i + l))
    (hc : ∀ l ∈ F, ∀ i, |Bc l i + V (i + l) / V i * Bc (-l) (i + l)| ≤ C₁ * h)
    (hLN : ∀ u : G → ℝ, ∑ i, u i * dop F β u i ≤ K * h * esq u)
    (hratio : ∀ l ∈ F, ∀ i, |(Real.sqrt (V i / V (i + l)) - 1) * β l i| ≤ C₃ * h)
    (hP₁ : ∀ U, ∑ i, V i * U i * P₁ U i ≤ C₂ * wip V U U) (U : G → ℝ) :
    ∑ i, V i * U i * (h⁻¹ * (dop F Bc U i + dop F β U i) + P₁ U i)
      ≤ (F.card * C₁ * (1 + ρ) / 4 + (K + F.card * C₃) + C₂) * wip V U U := by
  have h1 := dop_weighted_bound F hF Bc V hV hρ hc U
  have h2 := gaarding_transfer F β V hV hLN hratio U
  have h3 := hP₁ U
  have e : ∑ i, V i * U i * (h⁻¹ * (dop F Bc U i + dop F β U i) + P₁ U i)
      = h⁻¹ * (∑ i, V i * U i * dop F Bc U i + ∑ i, V i * U i * dop F β U i)
        + ∑ i, V i * U i * P₁ U i := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  have hw := wip_self_nonneg (fun i => (hV i).le) U
  have hhi : 0 < h⁻¹ := inv_pos.2 hh
  have : h⁻¹ * (∑ i, V i * U i * dop F Bc U i + ∑ i, V i * U i * dop F β U i)
      ≤ h⁻¹ * (F.card * (C₁ * h) * (1 + ρ) / 4 * wip V U U + (K + F.card * C₃) * h * wip V U U) := by
    gcongr; linarith
  have e2 : h⁻¹ * (F.card * (C₁ * h) * (1 + ρ) / 4 * wip V U U + (K + F.card * C₃) * h * wip V U U)
      = (F.card * C₁ * (1 + ρ) / 4 + (K + F.card * C₃)) * wip V U U := by
    field_simp
  linarith

/-- **Theorem 7.3 (stability on smoothly deformed lattices).** Under the hypotheses of
`deformed_energy`, every solution of `U' = L_h U` satisfies `‖U(t)‖_V ≤ e^{ωt}‖U(0)‖_V`. -/
theorem deformed_stability (F : Finset G) (hF : ∀ l ∈ F, -l ∈ F) (Bc β : G → G → ℝ)
    (P₁ : Matrix G G ℝ) (V : G → ℝ) (hV : ∀ i, 0 < V i) {h ρ C₁ C₂ C₃ K : ℝ} (hh : 0 < h)
    (hρ : ∀ l ∈ F, ∀ i, V i ≤ ρ * V (i + l))
    (hc : ∀ l ∈ F, ∀ i, |Bc l i + V (i + l) / V i * Bc (-l) (i + l)| ≤ C₁ * h)
    (hLN : ∀ u : G → ℝ, ∑ i, u i * dop F β u i ≤ K * h * esq u)
    (hratio : ∀ l ∈ F, ∀ i, |(Real.sqrt (V i / V (i + l)) - 1) * β l i| ≤ C₃ * h)
    (hP₁ : ∀ U, ∑ i, V i * U i * (P₁ *ᵥ U) i ≤ C₂ * wip V U U)
    (L : Matrix G G ℝ) (hL : ∀ U, L *ᵥ U = fun i => h⁻¹ * (dop F Bc U i + dop F β U i) + (P₁ *ᵥ U) i)
    {U : ℝ → G → ℝ} (hU : ∀ t, HasDerivAt U (L *ᵥ U t) t) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (wip V (U t) (U t)) ≤
      Real.exp ((F.card * C₁ * (1 + ρ) / 4 + (K + F.card * C₃) + C₂) * t) *
        Real.sqrt (wip V (U 0) (U 0)) := by
  have h := energy_bound_sqrt (W := diagonal V) (L := L) (diagonal_transpose V)
    (ω := F.card * C₁ * (1 + ρ) / 4 + (K + F.card * C₃) + C₂) (fun u => by
      rw [qf_diagonal]
      have := deformed_energy F hF Bc β (fun U => P₁ *ᵥ U) V hV hh hρ hc hLN hratio hP₁ u
      have e : u ⬝ᵥ (diagonal V *ᵥ (L *ᵥ u))
          = ∑ i, V i * u i * (h⁻¹ * (dop F Bc u i + dop F β u i) + (P₁ *ᵥ u) i) := by
        rw [hL]
        simp only [dotProduct, mulVec_diagonal]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]; exact this) hU ht
  simpa [qf_diagonal] using h

end Meshfree.Stability
