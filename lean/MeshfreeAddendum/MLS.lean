import MeshfreeAddendum.Taylor

/-!
# Moving least-squares derivative weights (Section 3 of the addendum)

A particle `i` is described by its finite neighbour set `J`, the offsets
`x : J → ℝ^D` (`x j = x_{ij}`) and the positive kernel weights `w : J → ℝ`
(`w j = w_{ij}`). All fits are *unregularized*: the weights are defined with the
exact inverse of the moment matrix. Regularized fits (Remark 3.2 / Remark 1.1(i))
are not modelled; for them the statements here do not apply.

* `divWeight q hq w x d j` is `c^{(d)}_{ij}` of eq. (3.2) `eq:cij`, degree `q ≥ 1`.
* Lemma 3.3   : `divWeight_reproduces`, `divWeight_sum_eq_zero`, `divWeight_dilate`.
* Lemma 3.5   : `divWeight_abs_le`, `sum_abs_divWeight_le`.
* Lemma 3.7   : `divWeight_antisymm`, `divWeight_reproduces_succ_of_odd`,
                `parity_fails_even` (the counterexample of (iii)).
* Corollary 3.8    : `derivative_error_le` (the algebraic core; Taylor's theorem is a
                hypothesis, see the docstring).
* Definition 3.9    : `qdiv` and its properties.
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree

variable {D : ℕ} {J : Type*} [Fintype J]

/-- The Taylor basis with constant term, `p̃_q(x_j)`, indexed by the multi-indices
of degree at most `q`. -/
noncomputable def taylorφ (D q : ℕ) (x : J → Pt D) : J → ↥(mis D q) → ℝ :=
  fun j α => mono α.1 (x j)

/-- Definition 3.1 (unisolvency), with polynomials of `Π_q` identified with their
coefficient vectors in the Taylor basis. -/
def UnisolventAt (q : ℕ) (x : J → Pt D) : Prop := Unisolvent (taylorφ D q x)

/-- The derivative weights `c^{(d)}_{ij} = w_{ij} e_{1+d}ᵀ Ñ_i⁻¹ p̃_q(x_{ij})`, eq. (3.2) `eq:cij`. -/
noncomputable def divWeight (q : ℕ) (hq : 1 ≤ q) (w : J → ℝ) (x : J → Pt D) (d : Fin D)
    (j : J) : ℝ :=
  lsWeight w (taylorφ D q x) ⟨unit d, unit_mem_mis hq d⟩ j

theorem taylorφ_dot {q : ℕ} (x : J → Pt D) (a : (Fin D → ℕ) → ℝ) (j : J) :
    taylorφ D q x j ⬝ᵥ (fun α => a α.1) = ∑ α ∈ mis D q, a α * mono α (x j) := by
  simp only [dotProduct, taylorφ]
  rw [← Finset.sum_coe_sort (mis D q)]
  exact Finset.sum_congr rfl fun α _ => mul_comm _ _

section Main

variable {q : ℕ} (hq : 1 ≤ q) {w : J → ℝ} {x : J → Pt D}

/-- **Lemma 3.3(i).** Unregularized derivative weights on a `Π_q`-unisolvent
neighbourhood differentiate polynomials of degree `≤ q` exactly. -/
theorem divWeight_reproduces (hw : ∀ j, 0 < w j) (hU : UnisolventAt q x)
    {g : Pt D → ℝ} (hg : g ∈ Poly D q) (d : Fin D) :
    ∑ j, divWeight q hq w x d j * g (x j) = pd g 0 d := by
  obtain ⟨a, ha⟩ := hg
  have hN := gram_isUnit w (taylorφ D q x) hw hU
  have h := lsWeight_reproduces hN (fun α => a α.1) ⟨unit d, unit_mem_mis hq d⟩
  simp only [taylorφ_dot] at h
  rw [pd_poly hq a g ha d, ← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha]; rfl

/-- **Lemma 3.3(ii).** Zero row sums. -/
theorem divWeight_sum_eq_zero (hw : ∀ j, 0 < w j) (hU : UnisolventAt q x) (d : Fin D) :
    ∑ j, divWeight q hq w x d j = 0 := by
  have hN := gram_isUnit w (taylorφ D q x) hw hU
  refine lsWeight_sum_eq_zero hN (e₀ := ⟨0, zero_mem_mis q⟩) (fun j => ?_) ?_
  · simp [taylorφ]
  · intro h
    exact unit_ne_zero d (congrArg Subtype.val h)

/-- **Lemma 3.3(iii).** Dilating the cloud by `θ ≠ 0` (with `R` scaled, so that the
kernel weights `w` are unchanged) divides the weights by `θ`. -/
theorem divWeight_dilate (θ : ℝ) (hθ : θ ≠ 0) (d : Fin D) (j : J) :
    divWeight q hq w (fun j => θ • x j) d j = θ⁻¹ * divWeight q hq w x d j := by
  have hφ : taylorφ D q (fun j => θ • x j) =
      fun j α => θ ^ deg α.1 * taylorφ D q x j α := by
    funext j α; simp [taylorφ, mono_smul]
  have h := lsWeight_scale (w := w) (φ := taylorφ D q x) (fun α => θ ^ deg α.1)
    (fun α => pow_ne_zero _ hθ) ⟨unit d, unit_mem_mis hq d⟩ j
  simp only [divWeight, hφ]
  rw [h, deg_unit, pow_one]

/-! ### Lemma 3.5: size of the weights -/

/-- **Lemma 3.5** (pointwise bound). Let `h > 0` and `xs = x/h` be the scaled offsets.
Hypotheses (Assumption 2.1 and the definition of `C_κ`):
* `0 ≤ w ≤ 1`;
* `hCN`: `‖(Ñ^s)⁻¹ v‖₂ ≤ C_N ‖v‖₂` for the scaled moment matrix (stated with squares);
* `hCκ`: `‖p̃_q(x_j/h)‖₂ ≤ C_κ` (stated with squares).
Then `|c^{(d)}_{ij}| ≤ C_N C_κ / h`. -/
theorem divWeight_abs_le {h : ℝ} (hh : 0 < h) (xs : J → Pt D) (hx : ∀ j, x j = h • xs j)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1) {CN Cκ : ℝ} (hCN0 : 0 ≤ CN) (hCκ0 : 0 ≤ Cκ)
    (hCN : ∀ v : ↥(mis D q) → ℝ,
      ∑ a, ((gram w (taylorφ D q xs))⁻¹ *ᵥ v) a ^ 2 ≤ CN ^ 2 * ∑ a, v a ^ 2)
    (hCκ : ∀ j, ∑ a, taylorφ D q xs j a ^ 2 ≤ Cκ ^ 2) (d : Fin D) (j : J) :
    |divWeight q hq w x d j| ≤ CN * Cκ / h := by
  have hxeq : x = fun j => h • xs j := funext hx
  rw [hxeq, divWeight_dilate hq h hh.ne' d j]
  set M := (gram w (taylorφ D q xs))⁻¹
  set e : ↥(mis D q) := ⟨unit d, unit_mem_mis hq d⟩
  have hsq : (M *ᵥ taylorφ D q xs j) e ^ 2 ≤ (CN * Cκ) ^ 2 := by
    calc (M *ᵥ taylorφ D q xs j) e ^ 2
        ≤ ∑ a, (M *ᵥ taylorφ D q xs j) a ^ 2 :=
          Finset.single_le_sum (f := fun a => (M *ᵥ taylorφ D q xs j) a ^ 2)
            (fun _ _ => sq_nonneg _) (mem_univ e)
      _ ≤ CN ^ 2 * ∑ a, taylorφ D q xs j a ^ 2 := hCN _
      _ ≤ CN ^ 2 * Cκ ^ 2 := by gcongr; exact hCκ j
      _ = (CN * Cκ) ^ 2 := by ring
  have habs : |(M *ᵥ taylorφ D q xs j) e| ≤ CN * Cκ :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hCN0 hCκ0)).1 (by rwa [sq_abs])
  simp only [divWeight, lsWeight]
  rw [abs_mul, abs_mul, abs_inv, abs_of_pos hh, abs_of_nonneg (hw0 j), div_eq_inv_mul]
  calc h⁻¹ * (w j * |(M *ᵥ taylorφ D q xs j) e|) ≤ h⁻¹ * (1 * (CN * Cκ)) := by
        gcongr
        · exact hw1 j
    _ = h⁻¹ * (CN * Cκ) := by ring

/-- **Lemma 3.5** (sum bound): `∑ⱼ ∑_d |c^{(d)}_{ij}| ≤ D N_max C_N C_κ / h`, with the
pointwise bound as hypothesis (it is `divWeight_abs_le`). -/
theorem sum_abs_le_of_abs_le (c : J → Fin D → ℝ) {B : ℝ} (hc : ∀ j d, |c j d| ≤ B)
    {Nmax : ℕ} (hN : Fintype.card J ≤ Nmax) (hB : 0 ≤ B) :
    ∑ j, ∑ d, |c j d| ≤ D * Nmax * B := by
  calc ∑ j, ∑ d, |c j d| ≤ ∑ _j : J, ∑ _d : Fin D, B :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun d _ => hc j d
    _ = Fintype.card J * (D * B) := by simp
    _ ≤ Nmax * (D * B) := by gcongr
    _ = D * Nmax * B := by ring

/-! ### Lemma 3.7: parity on centrally symmetric stencils -/

/-- A centrally symmetric neighbourhood: an involution (here any permutation suffices)
`ρ` with `x_{iρ(j)} = -x_{ij}`; then also `w_{iρ(j)} = w_{ij}` since `w` is radial. -/
structure CentrallySymmetric (w : J → ℝ) (x : J → Pt D) (ρ : Equiv.Perm J) : Prop where
  neg : ∀ j, x (ρ j) = - x j
  weight : ∀ j, w (ρ j) = w j

/-- **Lemma 3.7(i).** `c_{ij'} = -c_{ij}` on centrally symmetric stencils. -/
theorem divWeight_antisymm {ρ : Equiv.Perm J} (hS : CentrallySymmetric w x ρ)
    (d : Fin D) (j : J) : divWeight q hq w x d (ρ j) = - divWeight q hq w x d j := by
  refine lsWeight_reflect ρ (fun α => (-1) ^ deg α.1) (fun α => ?_) (fun j α => ?_)
    hS.weight ?_ j
  · rcases neg_one_pow_eq_or ℝ (deg α.1) with h | h <;> simp [h]
  · simp [taylorφ, hS.neg, mono_neg]
  · simp [deg_unit]

/-- **Lemma 3.7(ii).** For odd `q` on a centrally symmetric, `Π_q`-unisolvent
stencil, the weights differentiate polynomials of degree `q+1` exactly. -/
theorem divWeight_reproduces_succ_of_odd (hodd : Odd q) (hw : ∀ j, 0 < w j)
    (hU : UnisolventAt q x) {ρ : Equiv.Perm J} (hS : CentrallySymmetric w x ρ)
    {g : Pt D → ℝ} (hg : g ∈ Poly D (q + 1)) (d : Fin D) :
    ∑ j, divWeight q hq w x d j * g (x j) = pd g 0 d := by
  obtain ⟨a, ha⟩ := hg
  -- split `g` into its part of degree `≤ q` and its homogeneous part of degree `q+1`
  set top := (mis D (q + 1)).filter (fun α => deg α = q + 1)
  set glow : Pt D → ℝ := fun y => ∑ α ∈ mis D q, a α * mono α y
  set gtop : Pt D → ℝ := fun y => ∑ α ∈ top, a α * mono α y
  have hsplit : ∀ y, g y = glow y + gtop y := by
    intro y
    rw [ha]
    have hmis : mis D (q + 1) = (mis D (q + 1)).filter (fun α => ¬ deg α = q + 1) ∪ top := by
      rw [Finset.union_comm]; exact (Finset.filter_union_filter_not_eq _ _).symm
    have hlow : (mis D (q + 1)).filter (fun α => ¬ deg α = q + 1) = mis D q := by
      ext α; simp only [mem_filter, mem_mis]; omega
    rw [hmis, Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _).symm, hlow]
  have htop_even : ∀ y, gtop (-y) = gtop y := by
    intro y
    refine Finset.sum_congr rfl fun α hα => ?_
    have hdeg : deg α = q + 1 := (mem_filter.1 hα).2
    rw [mono_neg, hdeg, (Nat.even_add_one.2 (Nat.not_even_iff_odd.2 hodd)).neg_one_pow, one_mul]
  have hlow_eq : ∑ j, divWeight q hq w x d j * glow (x j) = a (unit d) := by
    rw [divWeight_reproduces hq hw hU ⟨a, fun y => rfl⟩ d, pd_poly hq a glow (fun y => rfl)]
  have htop_eq : ∑ j, divWeight q hq w x d j * gtop (x j) = 0 :=
    sum_odd_mul_even ρ _ _ (divWeight_antisymm hq hS d) (fun j _ => by rw [hS.neg, htop_even])
  rw [pd_poly (by omega) a g ha d]
  simp only [hsplit, mul_add, Finset.sum_add_distrib, hlow_eq, htop_eq, add_zero]

end Main

/-! ### Lemma 3.7(iii): the counterexample for even degree

`D = 1`, `q = 2`, offsets `-2, -1, 1, 2`, unit kernel weights and `g(y) = y³`:
the weights give `∑ⱼ cⱼ g(xⱼ) = 34/10 = 17/5 ≠ 0 = g'(0)`. -/

/-- The multi-indices of degree `≤ 2` in one dimension are `0, 1, 2`. -/
def misOneTwo : ↥(mis 1 2) ≃ Fin 3 where
  toFun α := ⟨α.1 0, by
    have := α.2; rw [mem_mis] at this; simp only [deg, Fin.sum_univ_one] at this; omega⟩
  invFun n := ⟨fun _ => n.1, by rw [mem_mis]; simp only [deg, Fin.sum_univ_one]; omega⟩
  left_inv α := by
    apply Subtype.ext; funext i; fin_cases i; rfl
  right_inv n := rfl

/-- Offsets of the counterexample. -/
def cexOffsets : Fin 4 → Pt 1 := ![fun _ => -2, fun _ => -1, fun _ => 1, fun _ => 2]

/-- The basis `(1, y, y²/2)` of the counterexample, indexed by `Fin 3`. -/
noncomputable def cexφ : Fin 4 → Fin 3 → ℝ :=
  fun j n => (cexOffsets j 0) ^ (n : ℕ) / ((n : ℕ).factorial : ℝ)


theorem cexφ_eq : (fun (j : Fin 4) (n : Fin 3) => taylorφ 1 2 cexOffsets j (misOneTwo.symm n))
    = cexφ := by
  funext j n
  simp [taylorφ, mono, cexφ, misOneTwo]

theorem parity_fails_even :
    ∑ j, divWeight 2 (by norm_num) (fun _ => 1) cexOffsets 0 j * (cexOffsets j 0) ^ 3
      = 17 / 5 := by
  -- reduce to the `Fin 3`-indexed basis
  have hre : ∀ j, divWeight 2 (by norm_num) (fun _ => 1) cexOffsets 0 j =
      lsWeight (fun _ => 1) cexφ 1 j := by
    intro j
    rw [← cexφ_eq, lsWeight_reindex]
    simp only [divWeight]
    congr 1
    apply Subtype.ext; funext i; fin_cases i; simp [misOneTwo, unit]
  simp only [hre]
  rw [← lsCoeff_apply]
  -- the moment matrix and the normal equations
  have hN : gram (fun _ => (1 : ℝ)) cexφ = !![4, 0, 5; 0, 10, 0; 5, 0, 17 / 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gram, cexφ, cexOffsets, Fin.sum_univ_four, Nat.factorial] <;> norm_num
  have hdet : IsUnit (gram (fun _ => (1 : ℝ)) cexφ).det := by
    rw [hN, Matrix.det_fin_three]; norm_num
  have hsol : gram (fun _ => (1 : ℝ)) cexφ *ᵥ ![0, 17 / 5, 0] =
      rhs (fun _ => 1) cexφ (fun j => cexOffsets j 0 ^ 3) := by
    rw [hN]
    funext a
    fin_cases a <;>
      simp [rhs, cexφ, cexOffsets, Fin.sum_univ_four, Fin.sum_univ_three, mulVec,
        dotProduct, Nat.factorial] <;> norm_num
  have : lsCoeff (fun _ => 1) cexφ (fun j => cexOffsets j 0 ^ 3) = ![0, 17 / 5, 0] := by
    rw [lsCoeff, ← hsol, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  rw [this]; rfl

/-- **Lemma 3.7(iii).** For even `q`, (ii) fails in general: the stencil above is
centrally symmetric and `Π_2`-unisolvent, but the degree-2 weights do not
differentiate `y³ ∈ Π_3` exactly. -/
theorem parity_fails_even' :
    ∑ j, divWeight 2 (by norm_num) (fun _ => 1) cexOffsets 0 j * (cexOffsets j 0) ^ 3
      ≠ pd (fun y : Pt 1 => y 0 ^ 3) 0 0 := by
  rw [parity_fails_even]
  have : pd (fun y : Pt 1 => y 0 ^ 3) 0 0 = 0 := by
    have hg : ∀ y : Pt 1, y 0 ^ 3 =
        ∑ α ∈ mis 1 3, (fun α : Fin 1 → ℕ => if α = (fun _ => 3) then (6 : ℝ) else 0) α *
          mono α y := by
      intro y
      rw [Finset.sum_eq_single (fun _ => 3)]
      · simp [mono, Nat.factorial]; ring
      · intro b _ hb; simp [hb]
      · intro h; exfalso; apply h; rw [mem_mis]; simp [deg]
    rw [pd_poly (q := 3) (by norm_num) _ _ hg 0]
    have : unit (0 : Fin 1) ≠ fun _ => 3 := by
      intro h; have := congrFun h 0; simp [unit] at this
    simp [this]
  rw [this]; norm_num

section Rest

variable {x : J → Pt D}

/-! ### Corollary 3.8: derivative error (algebraic core) -/

/-- **Corollary 3.8, algebraic core.** Suppose the weights `c` differentiate `Π_m`
exactly (`m = q` by Lemma 3.3(i); `m = q+1` for odd `q` on centrally symmetric
stencils by Lemma 3.7(ii)), satisfy `∑ⱼ |cⱼ| ≤ A / h` (Lemma 3.5), and let `g` be
approximated at the offsets by a polynomial `P ∈ Π_m` with `∂_d P(0) = ∂_d g(0)`
and remainder `|g(xⱼ) - g(0) - P(xⱼ)| ≤ C (κh)^{m+1}` (Taylor's theorem for smooth
`g` and `|xⱼ| ≤ κh`; this remainder bound is a *hypothesis* here, the
multivariate Taylor theorem is not formalized). Then the derivative error is at
most `A C κ^{m+1} h^m`, i.e. `O(h^m)`. -/
theorem derivative_error_le {m : ℕ} (c : J → ℝ) (d : Fin D)
    (hexact : ∀ P ∈ Poly D m, ∑ j, c j * P (x j) = pd P 0 d)
    {g P : Pt D → ℝ} (hP : P ∈ Poly D m) (hpd : pd P 0 d = pd g 0 d)
    {h κ A C : ℝ} (hh : 0 < h) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hsum : ∑ j, |c j| ≤ A / h)
    (hrem : ∀ j, |g (x j) - g 0 - P (x j)| ≤ C * (κ * h) ^ (m + 1)) :
    |∑ j, c j * (g (x j) - g 0) - pd g 0 d| ≤ A * C * κ ^ (m + 1) * h ^ m := by
  have hsplit : ∑ j, c j * (g (x j) - g 0) - pd g 0 d =
      ∑ j, c j * (g (x j) - g 0 - P (x j)) := by
    rw [← hpd, ← hexact P hP, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  have hA : 0 ≤ A / h := le_trans (Finset.sum_nonneg fun j _ => abs_nonneg (c j)) hsum
  calc |∑ j, c j * (g (x j) - g 0 - P (x j))|
      ≤ ∑ j, |c j| * |g (x j) - g 0 - P (x j)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ ≤ ∑ j, |c j| * (C * (κ * h) ^ (m + 1)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrem j) (abs_nonneg _)
    _ = (∑ j, |c j|) * (C * (κ * h) ^ (m + 1)) := by rw [Finset.sum_mul]
    _ ≤ A / h * (C * (κ * h) ^ (m + 1)) := by gcongr
    _ = A * C * κ ^ (m + 1) * h ^ m := by
        field_simp
        ring

end Rest

/-! ### Definition 3.9: the divergence degree -/

/-- `q(k) = 2⌈k/2⌉ - 1`. -/
def qdiv (k : ℕ) : ℕ := 2 * ((k + 1) / 2) - 1

theorem qdiv_odd {k : ℕ} (hk : 1 ≤ k) : Odd (qdiv k) := by
  rw [Nat.odd_iff]; unfold qdiv; omega

theorem qdiv_ge {k : ℕ} : k - 1 ≤ qdiv k := by unfold qdiv; omega

theorem one_le_qdiv {k : ℕ} (hk : 1 ≤ k) : 1 ≤ qdiv k := by unfold qdiv; omega

/-- `q(k)` is the smallest odd degree not below `k - 1`. -/
theorem qdiv_le_of_odd {k q : ℕ} (hq : Odd q) (h : k - 1 ≤ q) : qdiv k ≤ q := by
  rw [Nat.odd_iff] at hq; unfold qdiv; omega

theorem qdiv_of_even {k : ℕ} (hk : Even k) : qdiv k = k - 1 := by
  rw [Nat.even_iff] at hk; unfold qdiv; omega

theorem qdiv_of_odd {k : ℕ} (hk : Odd k) : qdiv k = k := by
  rw [Nat.odd_iff] at hk; unfold qdiv; omega

theorem qdiv_one : qdiv 1 = 1 := rfl
theorem qdiv_two : qdiv 2 = 1 := rfl

end Meshfree
