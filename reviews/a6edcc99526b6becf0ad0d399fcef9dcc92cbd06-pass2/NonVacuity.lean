import MeshfreeAddendum
import MeshfreeStability

/-!
# Review pass 2: extra checks (not part of the libraries)

Run from `lean/` with `lake env lean ../reviews/<sha>-pass2/NonVacuity.lean`.

1. The counterexample of Lemma 3.7(iii) satisfies the lemma's hypotheses: the stencil
   `±1, ±2` is `Π_2`-unisolvent and centrally symmetric (the README lists both as
   "true but not proved in Lean").
2. Some hypotheses of the main theorems are satisfiable for the intended instance
   (the Euler equations), so the theorems are not vacuous there.
-/

open Matrix Finset Meshfree

namespace Meshfree.ReviewPass2

/-- An invertible Gram matrix with nonzero weights gives unisolvency (converse direction of
`gram_isUnit`). -/
theorem unisolvent_of_gram_isUnit {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    {w : J → ℝ} {φ : J → ι → ℝ} (hN : IsUnit (gram w φ).det) : Unisolvent φ := by
  intro a ha
  have h0 : gram w φ *ᵥ a = 0 := by
    rw [gram_mulVec]; funext b; simp [ha]
  have hinj := (mulVec_injective_iff_isUnit).2 ((isUnit_iff_isUnit_det _).2 hN)
  exact hinj (by rw [h0, mulVec_zero])

theorem cex_gram_isUnit : IsUnit (gram (fun _ => (1 : ℝ)) cexφ).det := by
  have hN : gram (fun _ => (1 : ℝ)) cexφ = !![4, 0, 5; 0, 10, 0; 5, 0, 17 / 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gram, cexφ, cexOffsets, Fin.sum_univ_four, Nat.factorial] <;> norm_num
  rw [hN, Matrix.det_fin_three]; norm_num

/-- The stencil of `parity_fails_even` is `Π_2`-unisolvent. -/
theorem cex_unisolvent : UnisolventAt 2 cexOffsets := by
  have hU : Unisolvent cexφ := unisolvent_of_gram_isUnit cex_gram_isUnit
  intro a ha
  have h' : (fun n => a (misOneTwo.symm n)) = 0 := by
    apply hU
    intro j
    rw [← cexφ_eq]
    have := ha j
    simp only [dotProduct] at this ⊢
    rw [← this]
    exact Equiv.sum_comp misOneTwo.symm (fun α => taylorφ 1 2 cexOffsets j α * a α)
  funext α
  have := congrFun h' (misOneTwo α)
  simpa using this

/-- The stencil of `parity_fails_even` is centrally symmetric (involution `j ↦ 3 - j`). -/
theorem cex_centrallySymmetric :
    CentrallySymmetric (fun _ => (1 : ℝ)) cexOffsets Fin.revPerm := by
  refine ⟨fun j => ?_, fun j => rfl⟩
  funext i
  fin_cases j <;> fin_cases i <;> simp [cexOffsets, Fin.revPerm, Fin.rev]

/-- **Lemma 3.7(iii), complete**: a centrally symmetric, `Π_2`-unisolvent stencil with
positive weights on which the degree-2 weights do not differentiate `y³` exactly. -/
theorem parity_fails_even_full :
    (∀ j : Fin 4, (0 : ℝ) < (fun _ => (1 : ℝ)) j) ∧ UnisolventAt 2 cexOffsets ∧
      CentrallySymmetric (fun _ => (1 : ℝ)) cexOffsets Fin.revPerm ∧
      ∑ j, divWeight 2 (by norm_num) (fun _ => 1) cexOffsets 0 j * (cexOffsets j 0) ^ 3
        ≠ pd (fun y : Pt 1 => y 0 ^ 3) 0 0 :=
  ⟨fun _ => one_pos, cex_unisolvent, cex_centrallySymmetric, parity_fails_even'⟩

/-- The hypotheses `LFHyp` and `hlam` of Proposition 5.7 hold for the Euler equations. -/
theorem euler_prop57_hyps {D : ℕ} {γ : ℝ} (hγ : 1 < γ) :
    LFHyp (Euler.Adm (D := D) γ) (Euler.flux γ) (Euler.lam γ) ∧
      ∀ d U, U ∈ Euler.Adm (D := D) γ → 0 < Euler.lam γ d U :=
  ⟨Euler.lfHyp hγ, fun d _ hU => Euler.lam_pos hγ hU d⟩

/-- `Checkpoint.Local` and `hood C ⊇ C` are satisfiable (e.g. `hood = univ`), so the
hypotheses of Theorem 6.3 are not contradictory. -/
theorem checkpoint_hyps_satisfiable {I E : Type*} [Fintype I] [DecidableEq I]
    (W : (I → ℕ) → I → E) (bad : I → E → Prop) :
    let X : Checkpoint I E := ⟨W, bad, fun _ => univ⟩
    (∀ C, C ⊆ X.hood C) ∧ X.Local := by
  intro X
  exact ⟨fun C => subset_univ C, fun k C i hi => absurd (mem_univ i) hi⟩

end Meshfree.ReviewPass2

#print axioms Meshfree.ReviewPass2.parity_fails_even_full
#print axioms Meshfree.ReviewPass2.euler_prop57_hyps
#print axioms Meshfree.ReviewPass2.checkpoint_hyps_satisfiable
