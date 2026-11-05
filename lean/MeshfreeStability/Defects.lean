import MeshfreeStability.Deformed

/-!
# Section 8: deformed lattices with localised defects (1-D)

* **Lemma 8.1** (local squares): `squares_expand` (the sum of the local squares is the Toeplitz
  form with coefficients `∑_{k'} b_{k'} b_{k'+m}`) and `local_squares` (`eq:squares`). The
  existence of `b_g` (Fejér–Riesz with the outer factor) and its Lipschitz dependence on `g` are
  **hypotheses**.
* **Lemma 8.2**: `deformed_squares` (banded `O(h)` remainder). The entrywise `O(h)` estimates
  (Step 1 of Theorem 7.3 + Lipschitz `b_g`) are hypotheses.
* **Lemma 8.4** (support): `support_distances` (the distance bookkeeping of the proof).
* **Proposition 8.6** (the residual cannot be zero): `nsd_kernel`, `residual_zero_left_null`.
* **Theorem 8.7** (lattices with defects): `separation_disjoint` (the corrected separation
  `σ = 2ϱ + 2d + 12κ + 2`), `superposition_qf`, `defects_energy`, `defects_stability`.
  The certificates `W_{τ,g}` with residuals are **hypotheses** (computed by an SDP in floating
  point and checked a posteriori in floating point, not in Lean).
* **Corollary 8.8(i)**: `zone_radius_choice`, `defects_rate_bounded`.
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree.Stability

/-! ### Lemma 8.1 -/

section Squares

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The local square `B_j(u) = (∑_{k=0}^d b_k u_{j+k})²` on the periodic lattice `G` with unit
shift `e`. -/
def localSq (d : ℕ) (b : ℕ → ℝ) (e : G) (u : G → ℝ) (j : G) : ℝ :=
  (∑ k ∈ range (d + 1), b k * u (j + k • e)) ^ 2

/-- **Lemma 8.1, the expansion.** `∑_j B_j(u) = ∑_{k,k'} b_k b_{k'} ∑_i u_i u_{i+(k'-k)e}`: the
sum of the local squares is the periodic Toeplitz form whose coefficient at offset `m` is
`∑_{k'} b_{k'} b_{k'+m}`. -/
theorem squares_expand (d : ℕ) (b : ℕ → ℝ) (e : G) (u : G → ℝ) :
    ∑ j, localSq d b e u j = ∑ k ∈ range (d + 1), ∑ k' ∈ range (d + 1),
      b k * b k' * ∑ i, u i * u (i + ((k' : ℤ) - k) • e) := by
  simp only [localSq, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (k • e)) _ _ (fun j => ?_)
  simp only [Equiv.coe_addRight]
  rw [show j + k • e + ((k' : ℤ) - k) • e = j + k' • e by
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul]; abel]
  ring

/-- **Lemma 8.1, `eq:squares`.** If the coefficients match (`eq:fr`, provided by Fejér–Riesz),
i.e. the dissipation form `-uᵀ(VL+LᵀV)u` is the Toeplitz form of `b`, then it is the sum of the
local squares, hence `≥ 0`. -/
theorem local_squares (d : ℕ) (b : ℕ → ℝ) (e : G) (VL : Matrix G G ℝ)
    (hfr : ∀ u, -qf VL u = ∑ k ∈ range (d + 1), ∑ k' ∈ range (d + 1),
      b k * b k' * ∑ i, u i * u (i + ((k' : ℤ) - k) • e)) (u : G → ℝ) :
    -qf VL u = ∑ j, localSq d b e u j ∧ 0 ≤ -qf VL u := by
  rw [hfr, ← squares_expand]
  exact ⟨rfl, Finset.sum_nonneg fun j _ => sq_nonneg _⟩

/-- `b_g(1) = 0` (`m ≥ 1`) makes every local square vanish on constants. -/
theorem localSq_const (d : ℕ) (b : ℕ → ℝ) (e : G) (hb : ∑ k ∈ range (d + 1), b k = 0) (j : G) :
    localSq d b e (fun _ => 1) j = 0 := by
  simp [localSq, ← Finset.sum_mul, hb]

end Squares

/-! ### Lemma 8.2 -/

/-- **Lemma 8.2.** If `R = VL_h + L_hᵀV + ∑_j B_j^{(g_j)}` has at most `2·(2d)+1` nonzero entries
per row and column (bandwidth `2d`) and entries `≤ C h`, then
`uᵀ(VL_h + L_hᵀV)u ≤ -∑_j B_j(u) + (4d+1) C h |u|²`. -/
theorem deformed_squares {ι : Type*} [Fintype ι] [DecidableEq ι] (S B : Matrix ι ι ℝ)
    {d : ℕ} {C h : ℝ} (hR : ∀ i j, |(S + B) i j| ≤ C * h)
    (hrow : ∀ i, ((univ.filter fun j => (S + B) i j ≠ 0).card : ℝ) ≤ 4 * d + 1)
    (hcol : ∀ j, ((univ.filter fun i => (S + B) i j ≠ 0).card : ℝ) ≤ 4 * d + 1) (u : ι → ℝ) :
    qf S u ≤ -qf B u + (4 * d + 1) * (C * h) * esq u := by
  have h := banded_qf_le (S + B) hR hrow hcol u
  have e : qf (S + B) u = qf S u + qf B u := by simp [qf, add_mulVec, dotProduct_add]
  rw [e] at h
  linarith [le_abs_self (qf S u + qf B u)]

/-! ### Lemma 8.4 -/

/-- **Lemma 8.4, distance bookkeeping** (units of the spacing). Let `ρ₀ ≤ ϱ`, `d, κ ≥ 0`
(the assumption `d ≤ 4κ` of the note is not needed here),
`|y - z| > ϱ + d + 4κ` (`y ∉ Z'`). Then (a) every `y'` with `|y - y'| ≤ 2κ` is outside `Z` and
its row is a lattice row (`|y' - z| > ρ₀ + 2κ`); (b) every square through `y`
(`j ∈ [y-d, y]`) is far: its sites `j, …, j+d` are outside `Z`. -/
theorem support_distances {ρ₀ ϱ d κ y z : ℝ} (hϱ : ρ₀ ≤ ϱ) (hd0 : 0 ≤ d) (hκ : 0 ≤ κ)
    (hy : ϱ + d + 4 * κ < |y - z|) :
    (∀ y', |y - y'| ≤ 2 * κ → ϱ < |y' - z| ∧ ρ₀ + 2 * κ < |y' - z|) ∧
    (∀ j, y - d ≤ j → j ≤ y → ∀ k, 0 ≤ k → k ≤ d → ϱ < |j + k - z|) := by
  constructor
  · intro y' hy'
    have : |y - z| ≤ |y - y'| + |y' - z| := by
      calc |y - z| = |(y - y') + (y' - z)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have := abs_nonneg (y - y')
    constructor <;> linarith
  · intro j hj1 hj2 k hk0 hkd
    have : |y - z| ≤ |y - (j + k)| + |j + k - z| := by
      calc |y - z| = |(y - (j + k)) + (j + k - z)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have : |y - (j + k)| ≤ d := by rw [abs_le]; constructor <;> linarith
    linarith

/-! ### Proposition 8.6 -/

section Residual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A negative semidefinite symmetric matrix with `xᵀEx = 0` has `Ex = 0`. -/
theorem nsd_kernel (E : Matrix ι ι ℝ) (hE : Eᵀ = E) (hnsd : ∀ u, qf E u ≤ 0) (x : ι → ℝ)
    (hx : qf E x = 0) : E *ᵥ x = 0 := by
  -- `qf E (x + t y) = 2t yᵀEx + t² qf E y ≤ 0` for all `t` forces `yᵀEx = 0`
  have hbil : ∀ y : ι → ℝ, ∀ t : ℝ, qf E (x + t • y) = 2 * t * (y ⬝ᵥ (E *ᵥ x)) + t ^ 2 * qf E y := by
    intro y t
    have hsym : x ⬝ᵥ (E *ᵥ y) = y ⬝ᵥ (E *ᵥ x) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hE, dotProduct_comm]
    simp only [qf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [show x ⬝ᵥ (E *ᵥ x) = 0 from hx, hsym]; ring
  have hzero : ∀ y : ι → ℝ, y ⬝ᵥ (E *ᵥ x) = 0 := by
    intro y
    set a := y ⬝ᵥ (E *ᵥ x)
    set q := qf E y
    have h1 := hnsd (x + (1 : ℝ) • y)
    have h2 := hnsd (x + (-1 : ℝ) • y)
    rw [hbil] at h1 h2
    -- with `t = a / (|q| + 1)`
    have h3 := hnsd (x + (a / (|q| + 1)) • y)
    rw [hbil] at h3
    have hq : q ≤ 0 := hnsd y
    have hpos : 0 < |q| + 1 := by positivity
    have : 2 * (a / (|q| + 1)) * a + (a / (|q| + 1)) ^ 2 * q
        = a ^ 2 / (|q| + 1) * (2 + q / (|q| + 1)) := by field_simp
    rw [this] at h3
    have h4 : 0 < 2 + q / (|q| + 1) := by
      have : -1 < q / (|q| + 1) := by
        rw [lt_div_iff₀ hpos]; rw [abs_of_nonpos hq]; linarith
      linarith
    have : a ^ 2 / (|q| + 1) ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have : a ^ 2 ≤ 0 := by
      have := mul_le_mul_of_nonneg_right this hpos.le
      rwa [div_mul_cancel₀ _ hpos.ne', zero_mul] at this
    nlinarith [sq_nonneg a]
  ext i
  have := hzero (Pi.single i 1)
  simpa using this

/-- **Proposition 8.6.** Let `E = WL + LᵀW + B` with `W` symmetric, `L1 = 0` and `B1 = 0`
(the far squares vanish on constants, `localSq_const`). If `E ⪯ 0` (zero residual), then
`LᵀW1 = 0`: `W1` is a left null vector of `L`. Contrapositive: if `L` has no left null vector of
the form `W1` (constant outside the zone), the residual is positive. -/
theorem residual_zero_left_null (W L B : Matrix ι ι ℝ) (hW : Wᵀ = W) (hB : Bᵀ = B)
    (hL1 : L *ᵥ (fun _ => 1) = 0) (hB1 : B *ᵥ (fun _ => 1) = 0)
    (hnsd : ∀ u, qf (W * L + Lᵀ * W + B) u ≤ 0) : Lᵀ *ᵥ (W *ᵥ fun _ => 1) = 0 := by
  set E := W * L + Lᵀ * W + B
  have hE : Eᵀ = E := by
    simp only [E, transpose_add, transpose_mul, transpose_transpose, hW, hB]; abel
  have h1 : qf E (fun _ => 1) = 0 := by
    simp only [qf, E, add_mulVec, ← mulVec_mulVec, hL1, mulVec_zero, hB1, add_zero,
      dotProduct_add, dotProduct_zero, zero_add]
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, hL1, zero_dotProduct]
  have h2 := nsd_kernel E hE hnsd _ h1
  simp only [E, add_mulVec, ← mulVec_mulVec, hL1, mulVec_zero, hB1, add_zero, zero_add] at h2
  exact h2

end Residual

/-! ### Theorem 8.7 -/

/-- **Theorem 8.7, the separation.** With `σ = 2ϱ + 2d + 12κ + 2` (corrected value) and
`κ, ϱ, d ≥ 0`: (a) a particle within `ϱ + d + 6κ` of `z_A` is farther than `ϱ + d + 4κ` from any
other centre `z_B` (`|z_A - z_B| ≥ σ`), and more precisely at distance `≥ ϱ + d + 6κ + 2`;
(b) the blocks `Z''_A = {|s - z_A| ≤ ϱ + d + 6κ}` are pairwise disjoint. -/
theorem separation_disjoint {ϱ d κ zA zB : ℝ} (hκ : 0 ≤ κ)
    (hsep : 2 * ϱ + 2 * d + 12 * κ + 2 ≤ |zA - zB|) :
    (∀ s, |s - zA| ≤ ϱ + d + 4 * κ + 2 * κ → ϱ + d + 6 * κ + 2 ≤ |s - zB| ∧
        ϱ + d + 4 * κ < |s - zB|) ∧
    ∀ s, ¬ (|s - zA| ≤ ϱ + d + 6 * κ ∧ |s - zB| ≤ ϱ + d + 6 * κ) := by
  have tri : ∀ s, |zA - zB| ≤ |s - zA| + |s - zB| := fun s => by
    calc |zA - zB| = |(s - zB) - (s - zA)| := by ring_nf
      _ ≤ |s - zB| + |s - zA| := abs_sub _ _
      _ = _ := add_comm _ _
  refine ⟨fun s hs => ?_, fun s ⟨h1, h2⟩ => ?_⟩
  · have := tri s; constructor <;> linarith
  · have := tri s; linarith

section Superposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 8.7, superposition of the certificates.** `R = ∑_A R_A + R₀` with `R_A` supported
on pairwise disjoint blocks `S_A`, each satisfying the certificate inequality
`uᵀR_Au ≤ res_A |u_{S_A}|²` (Definition 8.5), and a remainder with `|uᵀR₀u| ≤ C'h|u|²`
(far pairs, `deformed_squares`). Then `uᵀRu ≤ (res* + C'h)|u|²`. -/
theorem superposition_qf {𝒜 : Type*} (A : Finset 𝒜) (S : 𝒜 → Finset ι)
    (hdisj : Set.PairwiseDisjoint (A : Set 𝒜) S) (RA : 𝒜 → Matrix ι ι ℝ) (R₀ : Matrix ι ι ℝ)
    (res : 𝒜 → ℝ) {resStar ε : ℝ} (hres : ∀ a ∈ A, res a ≤ resStar) (hres0 : 0 ≤ resStar)
    (hcert : ∀ a ∈ A, ∀ u, qf (RA a) u ≤ res a * ∑ i ∈ S a, u i ^ 2)
    (hR₀ : ∀ u, |qf R₀ u| ≤ ε * esq u) (u : ι → ℝ) :
    qf (∑ a ∈ A, RA a + R₀) u ≤ (resStar + ε) * esq u := by
  have hlin : qf (∑ a ∈ A, RA a + R₀) u = ∑ a ∈ A, qf (RA a) u + qf R₀ u := by
    simp only [qf, add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum]
  rw [hlin]
  have hblocks : ∑ a ∈ A, ∑ i ∈ S a, u i ^ 2 ≤ esq u := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _
  have h1 : ∑ a ∈ A, qf (RA a) u ≤ resStar * esq u := by
    calc ∑ a ∈ A, qf (RA a) u ≤ ∑ a ∈ A, resStar * ∑ i ∈ S a, u i ^ 2 := by
          refine Finset.sum_le_sum fun a ha => (hcert a ha u).trans ?_
          exact mul_le_mul_of_nonneg_right (hres a ha)
            (Finset.sum_nonneg fun i _ => sq_nonneg _)
      _ = resStar * ∑ a ∈ A, ∑ i ∈ S a, u i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ resStar * esq u := mul_le_mul_of_nonneg_left hblocks hres0
  have h2 := le_trans (le_abs_self _) (hR₀ u)
  linarith

/-- **Theorem 8.7, the energy inequality `eq:defects`.** If
`uᵀ(WL + LᵀW)u = -∑_{far} B_j(u) + uᵀRu` with nonnegative far squares, `uᵀRu ≤ ν |u|²` and
`uᵀWu ≥ c |u|²` (`c > 0`), then `uᵀWLu ≤ ν/(2c) · uᵀWu`. -/
theorem defects_energy (W L R Bfar : Matrix ι ι ℝ) (hW : Wᵀ = W) {c ν : ℝ} (hc : 0 < c)
    (hν : 0 ≤ ν) (hdec : ∀ u, qf (W * L + Lᵀ * W) u = -qf Bfar u + qf R u)
    (hB : ∀ u, 0 ≤ qf Bfar u) (hR : ∀ u, qf R u ≤ ν * esq u) (hWc : ∀ u, c * esq u ≤ qf W u)
    (u : ι → ℝ) : u ⬝ᵥ (W *ᵥ (L *ᵥ u)) ≤ ν / (2 * c) * qf W u := by
  have hsym : qf (W * L + Lᵀ * W) u = 2 * (u ⬝ᵥ (W *ᵥ (L *ᵥ u))) := by
    simp only [qf, add_mulVec, ← mulVec_mulVec, dotProduct_add]
    rw [dotProduct_mulVec u Lᵀ, ← mulVec_transpose, transpose_transpose, dotProduct_comm,
      dotProduct_mulVec, ← mulVec_transpose, hW]
    ring
  have h1 := hdec u
  rw [hsym] at h1
  have h2 := hB u
  have h3 := hR u
  have h4 := hWc u
  have hsq := esq_nonneg u
  have : ν * esq u ≤ ν / c * qf W u := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  have : u ⬝ᵥ (W *ᵥ (L *ᵥ u)) ≤ ν / 2 * esq u := by linarith
  calc u ⬝ᵥ (W *ᵥ (L *ᵥ u)) ≤ ν / 2 * esq u := this
    _ ≤ ν / (2 * c) * qf W u := by
      have e : ν / (2 * c) * qf W u = ν / 2 * (qf W u / c) := by field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [le_div_iff₀ hc]; linarith

/-- **Theorem 8.7, `eq:defectsbound`.** With the energy inequality of `defects_energy` (rate
`ω`) and the norm equivalence `c_V qf V ≤ qf W ≤ C_V qf V`, every solution satisfies
`‖U(t)‖²_V ≤ (C_V/c_V) e^{2ωt} ‖U(0)‖²_V`. -/
theorem defects_stability (W L : Matrix ι ι ℝ) (hW : Wᵀ = W) (V : ι → ℝ) {ω cV CV : ℝ}
    (hcV : 0 < cV) (hω : ∀ u, u ⬝ᵥ (W *ᵥ (L *ᵥ u)) ≤ ω * qf W u)
    (hlo : ∀ u, cV * wip V u u ≤ qf W u) (hhi : ∀ u, qf W u ≤ CV * wip V u u)
    {U : ℝ → ι → ℝ} (hU : ∀ t, HasDerivAt U (L *ᵥ U t) t) {t : ℝ} (ht : 0 ≤ t) :
    wip V (U t) (U t) ≤ CV / cV * Real.exp (2 * ω * t) * wip V (U 0) (U 0) := by
  have h := energy_bound hW hω hU ht
  have h1 := hlo (U t)
  have h2 := hhi (U 0)
  have he := Real.exp_pos (2 * ω * t)
  have h3 : cV * wip V (U t) (U t) ≤ CV * Real.exp (2 * ω * t) * wip V (U 0) (U 0) :=
    calc cV * wip V (U t) (U t) ≤ qf W (U t) := h1
      _ ≤ Real.exp (2 * ω * t) * qf W (U 0) := h
      _ ≤ Real.exp (2 * ω * t) * (CV * wip V (U 0) (U 0)) := mul_le_mul_of_nonneg_left h2 he.le
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hcV]; linarith

/-- **The constant in `eq:defectsbound`.** From `m₁ h |u|² ≤ uᵀW_hu ≤ M₁ h |u|²` (`eq:defects`,
`m₁ = min(c_W,1) g_-`, `M₁ = max(C_W,1) g_+`) and `g_- h ≤ V_i ≤ g_+ h`, the norm equivalence
needed by `defects_stability` holds with `c_V = m₁/g_+` and `C_V = M₁/g_-`, so the squared
constant is `C_V/c_V = M₁ g_+/(m₁ g_-) = max(C_W,1) g_+² / (min(c_W,1) g_-²)`. -/
theorem defects_norm_equiv (W : Matrix ι ι ℝ) (V : ι → ℝ) {m₁ M₁ gm gp h : ℝ}
    (hm₁ : 0 < m₁) (hM₁ : 0 ≤ M₁) (hgm : 0 < gm) (hgp : 0 < gp) (hh : 0 < h)
    (hWlo : ∀ u, m₁ * h * esq u ≤ qf W u) (hWhi : ∀ u, qf W u ≤ M₁ * h * esq u)
    (hVlo : ∀ i, gm * h ≤ V i) (hVhi : ∀ i, V i ≤ gp * h) (u : ι → ℝ) :
    m₁ / gp * wip V u u ≤ qf W u ∧ qf W u ≤ M₁ / gm * wip V u u := by
  have hsqV : wip V u u ≤ gp * h * esq u := by
    simp only [wip, esq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_right (hVhi i) (sq_nonneg (u i)); nlinarith
  have hsqV' : gm * h * esq u ≤ wip V u u := by
    simp only [wip, esq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_right (hVlo i) (sq_nonneg (u i)); nlinarith
  constructor
  · calc m₁ / gp * wip V u u ≤ m₁ / gp * (gp * h * esq u) :=
          mul_le_mul_of_nonneg_left hsqV (by positivity)
      _ = m₁ * h * esq u := by field_simp
      _ ≤ qf W u := hWlo u
  · calc qf W u ≤ M₁ * h * esq u := hWhi u
      _ = M₁ / gm * (gm * h * esq u) := by field_simp
      _ ≤ M₁ / gm * wip V u u := by
          exact mul_le_mul_of_nonneg_left hsqV' (by positivity)

end Superposition

/-! ### Corollary 8.8 -/

/-- **Corollary 8.8(i), the zone radius.** If `res(ϱ) ≤ C₀ e^{-cϱ}` and
`ϱ ≥ c⁻¹ log(C₀/(m h))` then `res(ϱ) ≤ m h`, so the excess rate `res*/(2 m h)` of Theorem 8.7
(with `m = min(c_W,1) g_-`) is at most `1/2`, uniformly in `h`. -/
theorem zone_radius_choice {C₀ c m h ϱ : ℝ} (hC₀ : 0 < C₀) (hc : 0 < c) (hm : 0 < m) (hh : 0 < h)
    (hϱ : Real.log (C₀ / (m * h)) / c ≤ ϱ) : C₀ * Real.exp (-(c * ϱ)) ≤ m * h := by
  have h1 : Real.log (C₀ / (m * h)) ≤ c * ϱ := by
    rw [div_le_iff₀ hc] at hϱ; linarith
  have h2 : Real.exp (-(c * ϱ)) ≤ Real.exp (-Real.log (C₀ / (m * h))) :=
    Real.exp_le_exp.2 (by linarith)
  have h2' : Real.exp (-Real.log (C₀ / (m * h))) = m * h / C₀ := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [h2'] at h2
  calc C₀ * Real.exp (-(c * ϱ)) ≤ C₀ * (m * h / C₀) := mul_le_mul_of_nonneg_left h2 hC₀.le
    _ = m * h := by field_simp

/-- Corollary 8.8(i): the resulting growth rate `C + res*/(2mh)` is bounded independently of
`h` (for `φ = id`, `C = 0` and the rate is `≤ 1/2`). -/
theorem defects_rate_bounded {C₀ c m h ϱ resStar Cdef : ℝ} (hC₀ : 0 < C₀) (hc : 0 < c)
    (hm : 0 < m) (hh : 0 < h) (hϱ : Real.log (C₀ / (m * h)) / c ≤ ϱ)
    (hres : resStar ≤ C₀ * Real.exp (-(c * ϱ))) :
    Cdef + resStar / (2 * m) * (1 / h) ≤ Cdef + 1 / 2 := by
  have := (hres.trans (zone_radius_choice hC₀ hc hm hh hϱ))
  have : resStar / (2 * m) * (1 / h) ≤ 1 / 2 := by
    rw [div_mul_div_comm, mul_one, div_le_iff₀ (by positivity)]; nlinarith
  linarith

end Meshfree.Stability
