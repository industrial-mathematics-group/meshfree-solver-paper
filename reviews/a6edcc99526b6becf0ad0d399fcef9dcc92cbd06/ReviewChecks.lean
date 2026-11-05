import MeshfreeAddendum
import MeshfreeStability

/-!
# Extra checks of the A2 review of commit a6edcc9 (5 Nov 2026)

Run from `lean/` with
`lake env lean ../reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06/ReviewChecks.lean`.

1. `#audit_axioms`: every declaration defined in `MeshfreeAddendum.*` or `MeshfreeStability.*`
   (not only those listed in the two `AxiomCheck.lean` files) uses at most
   `propext`, `Classical.choice`, `Quot.sound`.
2. The hypotheses of the Lemma 3.7(iii) counterexample (`Π_2`-unisolvency and central
   symmetry of the stencil `±1, ±2`), which `lean/README.md` lists as "not proved in Lean".
3. Non-vacuity of some central statements: their hypotheses can be met by concrete data.
-/

open Lean Elab Command in
/-- Collects the axioms of every constant whose module lies in one of the two libraries and
reports any axiom outside the standard three. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`MeshfreeAddendum).isPrefixOf mod || (`MeshfreeStability).isPrefixOf mod then
        if !name.isInternal then
          count := count + 1
          let axs ← liftCoreM <| Lean.collectAxioms name
          let extra := axs.filter (fun a => !ok.contains a)
          if !extra.isEmpty then bad := bad.push (name, extra)
  logInfo m!"audited {count} declarations; non-standard axioms in {bad.size}: {bad.toList}"

#audit_axioms

open Matrix

namespace Meshfree

/-! ## 2. The counterexample of Lemma 3.7(iii) satisfies the lemma's hypotheses -/

/-- An invertible moment matrix (for any weights) gives unisolvency. -/
theorem unisolvent_of_gram_isUnit {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    {w : J → ℝ} {φ : J → ι → ℝ} (hN : IsUnit (gram w φ).det) : Unisolvent φ := by
  intro a ha
  have h0 : gram w φ *ᵥ a = 0 := by
    rw [gram_mulVec]; funext b; simp [ha]
  have hinj : Function.Injective (gram w φ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hN)
  exact hinj (h0.trans (Matrix.mulVec_zero _).symm)

theorem cex_unisolvent : UnisolventAt 2 cexOffsets := by
  have hφ : taylorφ 1 2 cexOffsets = fun j α => cexφ j (misOneTwo α) := by
    funext j α
    rw [← cexφ_eq]; simp
  have hN : gram (fun _ => (1 : ℝ)) cexφ = !![4, 0, 5; 0, 10, 0; 5, 0, 17 / 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gram, cexφ, cexOffsets, Fin.sum_univ_four, Nat.factorial] <;> norm_num
  have hdet : IsUnit (gram (fun _ => (1 : ℝ)) cexφ).det := by
    rw [hN, Matrix.det_fin_three]; norm_num
  have hg : gram (fun _ => (1 : ℝ)) (taylorφ 1 2 cexOffsets)
      = (gram (fun _ => (1 : ℝ)) cexφ).submatrix misOneTwo misOneTwo := by
    ext a b; simp [gram, hφ]
  unfold UnisolventAt
  apply unisolvent_of_gram_isUnit (w := fun _ => (1 : ℝ))
  rw [hg, Matrix.det_submatrix_equiv_self]
  exact hdet

theorem cex_symmetric : CentrallySymmetric (fun _ => (1 : ℝ)) cexOffsets Fin.revPerm := by
  refine ⟨fun j => ?_, fun j => rfl⟩
  funext i
  fin_cases j <;> simp [cexOffsets, Fin.revPerm, Fin.rev]

/-- Hence Lemma 3.7(iii) as stated: a centrally symmetric, `Π_2`-unisolvent stencil with
positive weights on which (ii) fails for a polynomial of `Π_3`. -/
theorem lemma_3_7_iii :
    ∃ (x : Fin 4 → Pt 1) (w : Fin 4 → ℝ) (ρ : Equiv.Perm (Fin 4)),
      (∀ j, 0 < w j) ∧ UnisolventAt 2 x ∧ CentrallySymmetric w x ρ ∧
      (fun y : Pt 1 => y 0 ^ 3) ∈ Poly 1 3 ∧
      ∑ j, divWeight 2 (by norm_num) w x 0 j * (x j 0) ^ 3 ≠ pd (fun y : Pt 1 => y 0 ^ 3) 0 0 :=
  ⟨cexOffsets, fun _ => 1, Fin.revPerm, fun _ => one_pos, cex_unisolvent, cex_symmetric,
    ⟨fun α => if α = (fun _ => 3) then (6 : ℝ) else 0, fun y => by
      rw [Finset.sum_eq_single (fun _ => 3)]
      · simp [mono, Nat.factorial]; ring
      · intro b _ hb; simp [hb]
      · intro h; exfalso; apply h; rw [mem_mis]; simp [deg]⟩,
    parity_fails_even'⟩

/-! ## 3. Non-vacuity -/

/-- `divWeight_reproduces` and `divWeight_reproduces_succ_of_odd` have satisfiable
hypotheses (the stencil above is `Π_1`-unisolvent too, since it is `Π_2`-unisolvent). -/
example : ∑ j, divWeight 2 (by norm_num) (fun _ => 1) cexOffsets 0 j * (cexOffsets j 0) ^ 2
    = pd (fun y : Pt 1 => y 0 ^ 2) 0 0 := by
  have := divWeight_reproduces (q := 2) (by norm_num) (w := fun _ => (1 : ℝ))
    (fun _ => one_pos) cex_unisolvent
    (g := fun y : Pt 1 => y 0 ^ 2)
    ⟨fun α => if α = (fun _ => 2) then (2 : ℝ) else 0, fun y => by
      rw [Finset.sum_eq_single (fun _ => 2)]
      · simp [mono, Nat.factorial]; ring
      · intro b _ hb; simp [hb]
      · intro h; exfalso; apply h; rw [mem_mis]; simp [deg]⟩ 0
  simpa using this

/-- An admissible Euler state exists (so `Euler.Adm` is not empty), and the Euler instance
of the hypotheses of Propositions 5.2/5.7 type-checks. -/
example : ((1 : ℝ), (fun _ => 0 : Fin 1 → ℝ), (1 : ℝ)) ∈ Euler.Adm (D := 1) (7 / 5) := by
  refine ⟨by simp [Euler.rho], ?_⟩
  simp [Euler.pres, Euler.ener, Euler.msq, Euler.mom, Euler.rho]; norm_num

example {γ : ℝ} (hγ : 1 < γ) {D : ℕ} :
    Convex ℝ (Euler.Adm (D := D) γ) ∧ LFHyp (Euler.Adm (D := D) γ) (Euler.flux γ) (Euler.lam γ) ∧
      ∀ d (U : Euler.State D), U ∈ Euler.Adm γ → 0 < Euler.lam γ d U :=
  ⟨Euler.convex_Adm hγ, Euler.lfHyp hγ, fun d _ hU => Euler.lam_pos hγ hU d⟩

/-- `Checkpoint.run_admissible`: `hood = univ` satisfies `hhood` and `Local` (recheck everything);
then a checkpoint with a fallback that is admissible at order one ends admissible. -/
example {I : Type} [Fintype I] [DecidableEq I] (W : (I → ℕ) → I → ℝ) (G : Set ℝ)
    (hone : ∀ (k : I → ℕ) i, (∀ l, 1 ≤ k l) → k i = 1 → W k i ∈ G) (k₀ : I → ℕ)
    (hk₀ : ∀ i, 1 ≤ k₀ i) :
    let X : Checkpoint I ℝ := ⟨W, fun _ Z => Z ∉ G, fun _ => Finset.univ⟩
    ∀ i, X.W (X.run k₀ Finset.univ) i ∈ G := by
  intro X
  exact X.run_admissible (fun C => Finset.subset_univ C)
    (fun k C i hi => absurd (Finset.mem_univ i) hi) (fun _ _ h => h) hone k₀ hk₀

end Meshfree
