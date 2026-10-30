import MeshfreeAddendum.MLS

/-!
# The semi-discrete scheme (Section 4 of the addendum)

* `rusanov`                 : the Rusanov flux `eq:rusanov` with speed `s` and orientation `σ`.
* Lemma 4.1                 : `rusanov_swap`, `geometric_orientation_antisymm`,
                              `aligned_orientation_antisymm`.
* Reconstruction fits `eq:recfit` : `reconφ`, `recon_reproduces`.
* Proposition 4.2           : `exactness_linear`.
* Proposition 4.3           : only the algebraic steps are formalized
                              (`lattice_flux_parity`, `lattice_flux_cancel`); the
                              `O(h^k)` bookkeeping is not (see `README.md`).
* Proposition 4.4           : `conservation_balance`, `bracket_symm`, items (i)–(iii)
                              and the local-conservation consequence.
-/

open Finset Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Meshfree

/-! ### Rusanov flux and Lemma 4.1 -/

section Flux

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Rusanov flux `Φ_d(a, b; σ) = ½(F_d(a) + F_d(b)) - ½ s σ (b - a)`, eq. `eq:rusanov`. -/
noncomputable def rusanov (F : E → E) (s σ : ℝ) (a b : E) : E :=
  (1 / 2 : ℝ) • (F a + F b) - ((1 / 2 : ℝ) * s * σ) • (b - a)

/-- **Lemma 4.1**, core identity: `Φ_d(b, a; -σ) = Φ_d(a, b; σ)` for a symmetric
speed (here the same `s` on both sides). -/
theorem rusanov_swap (F : E → E) (s σ : ℝ) (a b : E) :
    rusanov F s (-σ) b a = rusanov F s σ a b := by
  unfold rusanov; module

/-- The speed `s = max{λ(a), λ(b)}` is symmetric. -/
theorem max_speed_symm (lam : E → ℝ) (a b : E) : max (lam a) (lam b) = max (lam b) (lam a) :=
  max_comm _ _

/-- **Lemma 4.1**, geometric edges: `sign(x_{ji,d}) = -sign(x_{ij,d})` since
`x_{ji} = -x_{ij}`. -/
theorem geometric_orientation_antisymm (x : ℝ) : Real.sign (-x) = - Real.sign x :=
  Real.sign_neg

/-- **Lemma 4.1**, aligned edges: strictly opposite signs of the weights give
opposite orientations. -/
theorem aligned_orientation_antisymm {a b : ℝ} (h : a * b < 0) :
    Real.sign b = - Real.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : 0 < b := by nlinarith [mul_pos_of_neg_of_neg ha ha]
    rw [Real.sign_of_neg ha, Real.sign_of_pos hb]; norm_num
  · subst ha; simp at h
  · have hb : b < 0 := by nlinarith [mul_pos ha ha]
    rw [Real.sign_of_neg hb, Real.sign_of_pos ha]

/-- If one weight vanishes and the other does not, the aligned orientations are not
opposite (why *strictly* opposite signs are required in Lemma 4.1). -/
theorem aligned_orientation_zero {b : ℝ} (hb : b ≠ 0) :
    Real.sign b ≠ - Real.sign 0 := by
  rw [Real.sign_zero, neg_zero]; exact fun h => hb (Real.sign_eq_zero_iff.1 h)

/-- **Lemma 4.1.** If `σ_{ji,d} = -σ_{ij,d}` and both sides evaluate the same two
interface states with the same symmetric speed, the two fluxes coincide. -/
theorem symmetric_interface_flux (F : E → E) (s σij σji : ℝ) (Uij Uji : E)
    (hσ : σji = -σij) : rusanov F s σji Uji Uij = rusanov F s σij Uij Uji := by
  rw [hσ, rusanov_swap]

end Flux

/-! ### Reconstruction fits and Proposition 4.2 -/

section Exactness

variable {D : ℕ} {J : Type*} [Fintype J]

/-- Multi-indices `1 ≤ |α| ≤ r` (the basis `p_r` without constant term). -/
def misPos (D r : ℕ) : Finset (Fin D → ℕ) := (mis D r).erase 0

/-- The reconstruction basis `p_r(x_j)` without constant term. -/
noncomputable def reconφ (D r : ℕ) (x : J → Pt D) : J → ↥(misPos D r) → ℝ :=
  fun j α => mono α.1 (x j)

/-- `Π_r`-unisolvency implies unisolvency of the basis without constant term. -/
theorem unisolvent_reconφ {r : ℕ} {x : J → Pt D} (hU : UnisolventAt r x) :
    Unisolvent (reconφ D r x) := by
  intro a ha
  classical
  let F : (Fin D → ℕ) → ℝ := fun α => if h : α ∈ misPos D r then a ⟨α, h⟩ else 0
  let a' : ↥(mis D r) → ℝ := fun α => F α.1
  have hdot : ∀ j, taylorφ D r x j ⬝ᵥ a' = reconφ D r x j ⬝ᵥ a := by
    intro j
    have h1 : taylorφ D r x j ⬝ᵥ a' = ∑ α ∈ mis D r, mono α (x j) * F α :=
      Finset.sum_coe_sort (mis D r) (fun α => mono α (x j) * F α)
    have h2 : reconφ D r x j ⬝ᵥ a = ∑ α ∈ misPos D r, mono α (x j) * F α := by
      rw [← Finset.sum_coe_sort (misPos D r)]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp [reconφ, F, α.2]
    rw [h1, h2]
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro α _ hα
    have hα' : α ∉ misPos D r := hα
    simp [F, hα']
  have h0 : a' = 0 := hU a' fun j => by rw [hdot]; exact ha j
  funext α
  have := congrFun h0 ⟨α.1, Finset.mem_of_mem_erase α.2⟩
  simpa [a', F, α.2] using this

/-- The reconstruction polynomial `R(y) = f_i + A_iᵀ p_r(y)` of the fit `eq:recfit`, for one
scalar component; `x` are the offsets `x_{ij}`, `f0 = f_i` and `f j = f_j`. -/
noncomputable def recon (r : ℕ) (w : J → ℝ) (x : J → Pt D) (f0 : ℝ) (f : J → ℝ)
    (y : Pt D) : ℝ :=
  f0 + ∑ α : ↥(misPos D r), lsCoeff w (reconφ D r x) (fun j => f j - f0) α * mono α.1 y

/-- Reproduction by the reconstruction fit (Section 3.1): if `g ∈ Π_r` and the data are
`f_j = g(x_{ij})`, `f_i = g(0)`, then `R(y) = g(y)` for all `y`. -/
theorem recon_reproduces {r : ℕ} {w : J → ℝ} {x : J → Pt D} (hw : ∀ j, 0 < w j)
    (hU : UnisolventAt r x) {g : Pt D → ℝ} (hg : g ∈ Poly D r) (y : Pt D) :
    recon r w x (g 0) (fun j => g (x j)) y = g y := by
  obtain ⟨a, ha⟩ := hg
  have hN := gram_isUnit w (reconφ D r x) hw (unisolvent_reconφ hU)
  have hsplit : ∀ z, g z = a 0 + ∑ α ∈ misPos D r, a α * mono α z := by
    intro z
    rw [ha, misPos, ← Finset.add_sum_erase _ _ (zero_mem_mis r), mono_zero, mul_one]
  have hdata : (fun j => g (x j) - g 0) = fun j => reconφ D r x j ⬝ᵥ (fun α => a α.1) := by
    funext j
    rw [hsplit (x j), hsplit 0]
    simp only [dotProduct, reconφ]
    rw [← Finset.sum_coe_sort (misPos D r)]
    have h0 : ∀ α ∈ misPos D r, mono α (0 : Pt D) = 0 := by
      intro α hα
      have hne : α ≠ 0 := Finset.ne_of_mem_erase hα
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h; push Not at h; exact hne (funext h)
      simp only [mono]
      exact Finset.prod_eq_zero (mem_univ i) (by simp [zero_pow hi])
    rw [Finset.sum_congr rfl (fun α hα => by rw [h0 α hα, mul_zero]) (s₁ := misPos D r)]
    simp only [Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  simp only [recon, hdata, lsCoeff_reproduces hN]
  rw [hsplit y, hsplit 0]
  have h0 : ∀ α ∈ misPos D r, mono α (0 : Pt D) = 0 := by
    intro α hα
    have hne : α ≠ 0 := Finset.ne_of_mem_erase hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h; push Not at h; exact hne (funext h)
    simp only [mono]
    exact Finset.prod_eq_zero (mem_univ i) (by simp [zero_pow hi])
  rw [Finset.sum_congr rfl (fun α hα => by rw [h0 α hα, mul_zero]) (s₁ := misPos D r)]
  simp only [Finset.sum_const_zero, add_zero]
  congr 1
  exact (Finset.sum_coe_sort (misPos D r) (fun α => a α * mono α y))

/-- Scaling a polynomial argument by `θ` keeps it in `Π_q` and multiplies the
first derivatives at `0` by `θ`. -/
theorem poly_comp_smul {q : ℕ} (hq : 1 ≤ q) {g : Pt D → ℝ} (hg : g ∈ Poly D q) (θ : ℝ) :
    (fun y => g (θ • y)) ∈ Poly D q ∧
      ∀ d, pd (fun y => g (θ • y)) 0 d = θ * pd g 0 d := by
  obtain ⟨a, ha⟩ := hg
  have hrep : ∀ y, g (θ • y) = ∑ α ∈ mis D q, (θ ^ deg α * a α) * mono α y := by
    intro y; rw [ha]
    exact Finset.sum_congr rfl fun α _ => by rw [mono_smul]; ring
  refine ⟨⟨_, hrep⟩, fun d => ?_⟩
  rw [pd_poly hq _ _ hrep, pd_poly hq a g ha, deg_unit, pow_one]

/-- **Proposition 4.2 (exactness for linear problems).**

Setting: particle `i` at `xi` with neighbour offsets `x j = x_{ij}` and kernel
weights `w`; linear fluxes `F_d(U) = A_d U`; `u : ℝ^D → ℝ^M` a polynomial of degree
`≤ k-1` (every component of `y ↦ u(xi + y)` lies in `Π_{k-1}`).

Hypotheses (a) and (c) of the proposition enter through the interface states: by
`recon_reproduces` (unisolvent, unregularized reconstruction fits, no limiter) the
reconstructions of `i` and of its neighbours reproduce `u`, so that
`U_{ij} = U_{ji} = u(m_{ij})`; this is hypothesis `hUij`, `hUji` here.
Hypothesis (b) is `hw`, `hU` and `hqk : k - 1 ≤ q`.

Conclusion: `L_i(U) = -∑_d A_d ∂_d u(x_i)`, for any orientation `σ` and speed `s`. -/
theorem exactness_linear {M q k : ℕ} (hq : 1 ≤ q) (hqk : k - 1 ≤ q)
    {w : J → ℝ} {x : J → Pt D} (hw : ∀ j, 0 < w j) (hU : UnisolventAt q x)
    (A : Fin D → Matrix (Fin M) (Fin M) ℝ) (xi : Pt D) (u : Pt D → Fin M → ℝ)
    (hu : ∀ m, (fun y => u (xi + y) m) ∈ Poly D (k - 1))
    (Uij Uji : J → Fin M → ℝ)
    (hUij : ∀ j, Uij j = u (xi + (1 / 2 : ℝ) • x j))
    (hUji : ∀ j, Uji j = u (xi + (1 / 2 : ℝ) • x j))
    (s σ : J → Fin D → ℝ) :
    (-(2 : ℝ)) • ∑ j, ∑ d, divWeight q hq w x d j •
        (rusanov (fun U => A d *ᵥ U) (s j d) (σ j d) (Uij j) (Uji j) - A d *ᵥ u xi)
      = - ∑ d, A d *ᵥ (fun m => pd (fun y => u y m) xi d) := by
  -- the dissipation vanishes and the flux is `A_d u(m_{ij})`
  have hflux : ∀ j d, rusanov (fun U => A d *ᵥ U) (s j d) (σ j d) (Uij j) (Uji j)
      = A d *ᵥ u (xi + (1 / 2 : ℝ) • x j) := by
    intro j d
    simp only [rusanov, hUij, hUji, sub_self, smul_zero, sub_zero]
    rw [← two_smul ℝ, smul_smul]; norm_num
  simp only [hflux, ← mulVec_sub]
  -- componentwise: the derivative weights differentiate `y ↦ u(xi + y/2)`
  have hcomp : ∀ d m, ∑ j, divWeight q hq w x d j *
      (u (xi + (1 / 2 : ℝ) • x j) m - u xi m) = (1 / 2 : ℝ) * pd (fun y => u y m) xi d := by
    intro d m
    have hpoly : (fun y => u (xi + y) m) ∈ Poly D q := Poly.mono hqk (hu m)
    obtain ⟨hpoly2, hpd2⟩ := poly_comp_smul hq hpoly (1 / 2)
    have hsum := divWeight_sum_eq_zero hq hw hU d
    have hrep := divWeight_reproduces hq hw hU hpoly2 d
    rw [pd_shift, ← hpd2 d, ← hrep]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  funext m
  simp only [Finset.smul_sum, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mulVec, dotProduct]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hx : ∑ j, divWeight q hq w x d j * ∑ l, A d m l * (u (xi + (1 / 2 : ℝ) • x j) - u xi) l
      = ∑ l, A d m l * ∑ j, divWeight q hq w x d j *
          (u (xi + (1 / 2 : ℝ) • x j) l - u xi l) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.sub_apply]; ring
  rw [hx]
  simp only [hcomp]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Exactness

/-! ### Proposition 4.3: the algebraic steps -/

section Lattice

variable {J : Type*} [Fintype J] {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Proposition 4.3, step "Fluxes".** With the reconstruction error `E` of parity
`(-1)^k` and an odd orientation `ς`, the leading flux error
`G(y) = ½(1+(-1)^k) F'(u) E(y) + ½(1-(-1)^k) λ ς(y) E(y)` is even. -/
theorem lattice_flux_parity {Y : Type*} [Neg Y] (k : ℕ) (Fp : E →ₗ[ℝ] E) (lam : ℝ)
    (Err : Y → E) (ς : Y → ℝ) (hE : ∀ y, Err (-y) = (-1 : ℝ) ^ k • Err y)
    (hς : ∀ y, ς (-y) = - ς y) (y : Y) :
    let G := fun y => ((1 / 2 : ℝ) * (1 + (-1) ^ k)) • Fp (Err y)
      + ((1 / 2 : ℝ) * (1 - (-1) ^ k) * lam * ς y) • Err y
    G (-y) = G y := by
  intro G
  simp only [G, hE, hς, map_smul, smul_smul]
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> module

/-- **Proposition 4.3, step "Summation".** On a lattice the weights are odd under the
central reflection (Lemma 3.7(i)) and the flux errors `G` are even wherever the
weight is non-zero, so they drop out of the divergence. -/
theorem lattice_flux_cancel (ρ : Equiv.Perm J) (c : J → ℝ) (G : J → E)
    (hc : ∀ j, c (ρ j) = - c j) (hG : ∀ j, c j ≠ 0 → G (ρ j) = G j) :
    ∑ j, c j • G j = 0 := by
  have h : ∑ j, c j • G j = ∑ j, c (ρ j) • G (ρ j) := (Equiv.sum_comp ρ _).symm
  have h' : ∑ j, c (ρ j) • G (ρ j) = - ∑ j, c j • G j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : c j = 0
    · simp [hc, hj]
    · rw [hc, hG j hj, neg_smul]
  have : (2 : ℝ) • ∑ j, c j • G j = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; rw [h', neg_add_cancel]
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

end Lattice

/-! ### Proposition 4.4: conservation balance -/

section Conservation

variable {P : Type*} [DecidableEq P] {D : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Data of the conservation analysis. `st i j = U_{ij}` are the interface states,
`c i j d = c^{(d)}_{ij}`, `σ i j d = σ_{ij,d}`, `s i j d = s_{ij,d}`. -/
structure ConsData (P : Type*) (D : ℕ) (E : Type*) where
  nb : P → Finset P
  V : P → ℝ
  c : P → P → Fin D → ℝ
  σ : P → P → Fin D → ℝ
  s : P → P → Fin D → ℝ
  st : P → P → E
  F : Fin D → E → E

namespace ConsData

variable (S : ConsData P D E)

/-- The interface flux `F*_{ij,d}`. -/
noncomputable def Fstar (i j : P) (d : Fin D) : E :=
  rusanov (S.F d) (S.s i j d) (S.σ i j d) (S.st i j) (S.st j i)

/-- The scheme `L_i = -2 ∑_j c_{ij} · F*_{ij}` (zero-row-sum form of `eq:scheme`). -/
noncomputable def L (i : P) : E := (-(2 : ℝ)) • ∑ j ∈ S.nb i, ∑ d, S.c i j d • S.Fstar i j d

/-- Pair defect `d_{ij,d} = V_i c_{ij} + V_j c_{ji}`. -/
def dDef (i j : P) (d : Fin D) : ℝ := S.V i * S.c i j d + S.V j * S.c j i d

/-- Pair defect `e_{ij,d} = V_i σ_{ij} c_{ij} - V_j σ_{ji} c_{ji}`. -/
def eDef (i j : P) (d : Fin D) : ℝ :=
  S.V i * S.σ i j d * S.c i j d - S.V j * S.σ j i d * S.c j i d

/-- The bracket of `eq:balance`. -/
noncomputable def bracket (i j : P) (d : Fin D) : E :=
  S.dDef i j d • (S.F d (S.st i j) + S.F d (S.st j i))
    - (S.s i j d * S.eDef i j d) • (S.st j i - S.st i j)

/-- The bracket is symmetric, so the sum over ordered interior pairs with factor `½`
equals the sum over unordered pairs in `eq:balance`. -/
theorem bracket_symm (hs : ∀ i j d, S.s j i d = S.s i j d) (i j : P) (d : Fin D) :
    S.bracket j i d = S.bracket i j d := by
  simp only [bracket, dDef, eDef, hs j i]
  module

theorem pair_identity (hs : ∀ i j d, S.s j i d = S.s i j d) (i j : P) (d : Fin D) :
    S.V i • ((-(2 : ℝ)) • (S.c i j d • S.Fstar i j d))
      + S.V j • ((-(2 : ℝ)) • (S.c j i d • S.Fstar j i d)) = - S.bracket i j d := by
  simp only [bracket, dDef, eDef, Fstar, rusanov, hs j i]
  module

/-- **Proposition 4.4 (conservation balance).** For any interface states, orientations,
symmetric speeds and weights (the zero row sums are used only to write the scheme as
`L_i = -2∑ⱼ c_{ij}·F*_{ij}`, which is the definition `L` here):
`∑_{i∈I} V_i L_i = -2 ∑_{i∈I} ∑_{j∈ν(i)∖I} V_i c_{ij}·F*_{ij}
                   - ½ ∑_{i∈I} ∑_{j∈ν(i)∩I} ∑_d bracket_{ij,d}`. -/
theorem conservation_balance (I : Finset P) (hnb : ∀ i j, j ∈ S.nb i ↔ i ∈ S.nb j)
    (hs : ∀ i j d, S.s j i d = S.s i j d) :
    ∑ i ∈ I, S.V i • S.L i =
      (-(2 : ℝ)) • ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∉ I), S.V i • ∑ d, S.c i j d • S.Fstar i j d
      - (1 / 2 : ℝ) • ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), ∑ d, S.bracket i j d := by
  set x : P → P → E := fun i j => S.V i • ((-(2 : ℝ)) • ∑ d, S.c i j d • S.Fstar i j d)
  have hL : ∀ i, S.V i • S.L i = ∑ j ∈ (S.nb i).filter (· ∈ I), x i j
      + ∑ j ∈ (S.nb i).filter (· ∉ I), x i j := by
    intro i
    rw [Finset.sum_filter_add_sum_filter_not]
    simp only [x, L, Finset.smul_sum]
  have hswap : ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), x i j
      = ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), x j i := by
    refine Finset.sum_comm' fun i j => ?_
    simp only [mem_filter]
    constructor
    · rintro ⟨hi, hj, hjI⟩; exact ⟨⟨(hnb i j).1 hj, hi⟩, hjI⟩
    · rintro ⟨⟨hj, hi⟩, hjI⟩; exact ⟨hi, (hnb i j).2 hj, hjI⟩
  have hpair : ∀ i j, x i j + x j i = - ∑ d, S.bracket i j d := by
    intro i j
    simp only [x, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => S.pair_identity hs i j d
  have hint : ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), x i j
      = - (1 / 2 : ℝ) • ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), ∑ d, S.bracket i j d := by
    have h2 : (2 : ℝ) • ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), x i j
        = - ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), ∑ d, S.bracket i j d := by
      rw [two_smul]; nth_rewrite 2 [hswap]
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => hpair i j
    have : ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), x i j
        = (1 / 2 : ℝ) • ((2 : ℝ) • ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), x i j) := by
      rw [smul_smul]; norm_num
    rw [this, h2, smul_neg, neg_smul]
  simp only [hL, Finset.sum_add_distrib, hint]
  simp only [x, Finset.smul_sum, smul_comm (S.V _) (-(2 : ℝ))]
  simp only [neg_smul, Finset.sum_neg_distrib, smul_neg]
  abel

/-- **Proposition 4.4(i).** Geometric edges with `x_{ij,d} ≠ 0`:
`σ_{ji} = -σ_{ij} ∈ {±1}` gives `e = σ_{ij} d` and `|e| ≤ |d|`. -/
theorem eDef_geometric (i j : P) (d : Fin D) (hσ : S.σ j i d = - S.σ i j d)
    (hpm : S.σ i j d = 1 ∨ S.σ i j d = -1) :
    S.eDef i j d = S.σ i j d * S.dDef i j d ∧ |S.eDef i j d| ≤ |S.dDef i j d| := by
  have he : S.eDef i j d = S.σ i j d * S.dDef i j d := by
    simp only [eDef, dDef, hσ]; ring
  refine ⟨he, ?_⟩
  rw [he, abs_mul]
  rcases hpm with h | h <;> simp [h]

theorem sign_mul_self (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · subst h; simp
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

/-- **Proposition 4.4(ii).** Aligned edges (each particle orients by the sign of its own
weight): `e = V_i|c_{ij}| - V_j|c_{ji}|` and `|e| ≤ |d|` (positive volumes). -/
theorem eDef_aligned (i j : P) (d : Fin D) (hσi : S.σ i j d = Real.sign (S.c i j d))
    (hσj : S.σ j i d = Real.sign (S.c j i d)) (hVi : 0 < S.V i) (hVj : 0 < S.V j) :
    S.eDef i j d = S.V i * |S.c i j d| - S.V j * |S.c j i d| ∧
      |S.eDef i j d| ≤ |S.dDef i j d| := by
  have he : S.eDef i j d = S.V i * |S.c i j d| - S.V j * |S.c j i d| := by
    simp only [eDef, hσi, hσj, mul_assoc, sign_mul_self]
  refine ⟨he, ?_⟩
  rw [he, dDef]
  have h1 : S.V i * |S.c i j d| = |S.V i * S.c i j d| := by rw [abs_mul, abs_of_pos hVi]
  have h2 : S.V j * |S.c j i d| = |-(S.V j * S.c j i d)| := by
    rw [abs_neg, abs_mul, abs_of_pos hVj]
  rw [h1, h2]
  have := abs_abs_sub_abs_le_abs_sub (S.V i * S.c i j d) (-(S.V j * S.c j i d))
  simpa [sub_neg_eq_add] using this

/-- **Proposition 4.4(iii).** Geometric edges with `x_{ij,d} = 0` and the convention
`σ_{ij} = σ_{ji} = -1`: `e = V_j c_{ji} - V_i c_{ij}`. -/
theorem eDef_convention (i j : P) (d : Fin D) (hσi : S.σ i j d = -1) (hσj : S.σ j i d = -1) :
    S.eDef i j d = S.V j * S.c j i d - S.V i * S.c i j d := by
  simp only [eDef, hσi, hσj]; ring

/-- … and it is not bounded by `|d|` in general: `V = 1`, `c_{ij} = 1`, `c_{ji} = -1`
gives `d = 0` and `e = -2`. -/
theorem eDef_convention_unbounded :
    ∃ (Vi Vj cij cji : ℝ), 0 < Vi ∧ 0 < Vj ∧
      ¬ |Vj * cji - Vi * cij| ≤ |Vi * cij + Vj * cji| :=
  ⟨1, 1, 1, -1, one_pos, one_pos, by norm_num⟩

/-- Local conservation: if all pair defects of interior pairs vanish, the interior
sum in `eq:balance` vanishes and only the boundary term remains. -/
theorem local_conservation (I : Finset P) (hnb : ∀ i j, j ∈ S.nb i ↔ i ∈ S.nb j)
    (hs : ∀ i j d, S.s j i d = S.s i j d)
    (hd : ∀ i ∈ I, ∀ j ∈ S.nb i, j ∈ I → ∀ d, S.dDef i j d = 0 ∧ S.eDef i j d = 0) :
    ∑ i ∈ I, S.V i • S.L i =
      (-(2 : ℝ)) • ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∉ I),
        S.V i • ∑ d, S.c i j d • S.Fstar i j d := by
  rw [S.conservation_balance I hnb hs]
  have : ∑ i ∈ I, ∑ j ∈ (S.nb i).filter (· ∈ I), ∑ d, S.bracket i j d = 0 := by
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [mem_filter] at hj
    refine Finset.sum_eq_zero fun d _ => ?_
    obtain ⟨h1, h2⟩ := hd i hi j hj.1 hj.2 d
    simp [bracket, h1, h2]
  rw [this, smul_zero, sub_zero]

/-- Antisymmetric face vectors `V_i c_{ij} = -V_j c_{ji}` give `d = 0`, and then `e = 0`
on geometric edges with `x_{ij,d} ≠ 0` (by (i)) and on aligned edges (by (ii)). -/
theorem defects_vanish_of_antisymm (i j : P) (d : Fin D)
    (hanti : S.V i * S.c i j d = - (S.V j * S.c j i d))
    (horient : (S.σ j i d = - S.σ i j d ∧ (S.σ i j d = 1 ∨ S.σ i j d = -1)) ∨
      (S.σ i j d = Real.sign (S.c i j d) ∧ S.σ j i d = Real.sign (S.c j i d) ∧
        0 < S.V i ∧ 0 < S.V j)) :
    S.dDef i j d = 0 ∧ S.eDef i j d = 0 := by
  have hd : S.dDef i j d = 0 := by simp only [dDef, hanti]; ring
  refine ⟨hd, ?_⟩
  rcases horient with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · rw [(S.eDef_geometric i j d h1 h2).1, hd, mul_zero]
  · have := (S.eDef_aligned i j d h1 h2 h3 h4).2
    rw [hd, abs_zero] at this
    exact abs_nonpos_iff.1 this

end ConsData

end Conservation

end Meshfree
