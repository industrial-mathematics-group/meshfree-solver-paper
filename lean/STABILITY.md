# Lean formalization of the stability note (Part I)

Lean 4 (v4.35.0) + Mathlib (tag `v4.35.0`) formalization of the proved results of Part I
(Sections 3 to 9, partially) of `stability/stability_combined.tex`, the revised version of
29 Oct 2026. Part II is not covered. The library is `MeshfreeStability`. It sits next to
`MeshfreeAddendum` in this Lake project and reuses its definitions (`Checkpoint`,
`scalar_led`, `ssp_stages`, `rusanov`, `LFHyp`, `Euler.State`, ...).

## Status

`lake build` succeeds with **no `sorry`, no `admit` and no extra axioms** (2,975 lines in
10 files). `MeshfreeStability/AxiomCheck.lean` prints the axioms of 77 main results. Each one
depends only on `propext`, `Classical.choice` and `Quot.sound`, Lean's standard axioms.

Priority, as agreed: the formalization checks that the **analysis** behind the implementation
is right. Results that the paper obtains by computer (SDP certificates, the `P_nm` polynomial
inequalities, `N ≤ 64` checks) or cites from the literature (Lax–Nirenberg, Fejér–Riesz,
Perron–Frobenius, Riemann-problem facts) enter as **explicit hypotheses** of the Lean
theorems. In several rows (Thms 3.1, 4.4, 6.1, 7.3, 8.7, Lemma 8.1, Prop 3.3, Prop 4.3, Cor 6.4) proof steps
that the paper proves itself also enter as hypotheses; the table lists them. Every such hypothesis is a named
argument, so it is visible in the statement.

Legend for the table:

* **Checked**: Lean proves the statement as in the paper.
* **Checked, hyp.**: Lean proves the statement, with the listed input as a hypothesis.
* **Partial**: part of the statement is checked; the rest is listed.
* **Not done**: not formalized.

## Building

```
lake build                                   # builds both libraries
lake env lean MeshfreeStability/AxiomCheck.lean
```
`cache.mathlib.org` was blocked in this environment, so Mathlib was compiled from source
(about 2,570 Mathlib modules; Lake runs about 2,900 jobs in total). The toolchain came from the GitHub release of Lean v4.35.0.

## Modelling choices

* A linear semi-discrete scheme is a matrix `L : Matrix ι ι ℝ` on a finite particle set `ι`.
  Stability is stated for **every solution** `U : ℝ → ι → ℝ` with `U' = L U`. This is the same
  as a bound on `‖e^{tL}‖`, because `t ↦ e^{tL} U₀` is a solution (`linear_ode_exists`).
* Energies: `qf W u = uᵀWu` for a symmetric weight matrix, `wip H u v = ∑ H_i u_i v_i` for
  diagonal weights (the norms `‖·‖_V`, `‖·‖_π`, `‖·‖_H` of the note), `esq u = ∑ u_i²`.
* Lattices and periodic grids are finite abelian groups (`ZMod N`, or any `G`), so the
  periodic setting of the note is exact and sums can be shifted freely.
* Section 3 uses the addendum's model: states in a real vector space with a convex admissible
  set `G`, the checkpoint/override logic of Algorithm 1, the Lax–Friedrichs hypothesis
  `LFHyp`.

## Statement-by-statement status

| Statement | Lean names | Status |
|---|---|---|
| **Thm 3.1** max. principle of stage-wise MOOD | `dmp_checkpoint`, `scalar_led_local_range`, `stagewise_mood_max_principle` | Checked, hyp.: Prop 5.7 of the addendum at every checkpoint (range form, `hone`), exact locality of the checkpoint (`hloc`) and the Shu–Osher form of the stages (`hSO`); nothing links `Checkpoint.W` to `schemeOp`. Same label as the analogous addendum Thm 6.3 |
| **Prop 3.3** ℓ¹ bounds for Euler | `euler_l1_bounds`, `euler_l1_bounds_defect` (with defect `Δⁿ`) | Checked, hyp.: the relation `Mⁿ = M⁰ + Δⁿ`, which the paper derives from the discrete balance (addendum Prop 4.4) over the RK stages; that step is not formalized |
| **Prop 3.5** local entropy inequality | `riemannAvg_identity`, `local_entropy_inequality` | Checked, hyp.: the Riemann-problem facts (Riemann average in `G`, entropy inequality for the exact solution) |
| **Cor 3.7** global entropy balance | `global_entropy_balance`, `global_entropy_nonincreasing`, `ssp_convex_functional` | Checked, hyp.: inherits the Riemann-problem hypotheses of Prop 3.5; the clause for linear symmetric systems is not formalized separately |
| **Thm 4.1(i)** `q ≥ 0`, generator, max. principle | `qcoef_nonneg`, `genMat_mulVec`, `genMat_one`, `markov_max_principle` | Checked |
| **Thm 4.1(ii)** stationary `π`, conservation | `stationary_iff`, `stationary_conserved` | Partial: conservation checked; existence/uniqueness of `π > 0` (Perron–Frobenius) is a hypothesis |
| **Thm 4.1(iii)** energy identity, `π`-norm contraction | `markov_energy_identity`, `markov_L2_contraction` | Partial: identity and `p = 2` checked; continuous-time `p ≠ 2` not done |
| **Thm 4.1(iv)** forward Euler / SSP-RK, all `1 ≤ p ≤ ∞` | `euler_step_max`, `euler_step_contraction_p`, `rk_contraction_p` | Partial: forward Euler for all `1 ≤ p ≤ ∞`; the SSP-RK statement `rk_contraction_p` covers finite `p ≥ 1` only, the case `p = ∞` is not stated for Runge–Kutta |
| **Thm 4.1(v)** volume-norm bound | `markov_volume_bound` | Partial: the continuous-time bound is checked; the same bound for the discrete steps of (iv), which the statement also claims, is not formalized (it would follow from `rk_contraction_p` with `p = 2`) |
| **Prop 4.3** truncation error | `truncation_identity`, `remainder_le`, `beta_zero_of_symmetric` | Checked, hyp.: the `O(h)` remainder bound needs the Taylor bound and addendum Lemma 3.5, which are not linked |
| **Thm 4.4** drift | `corrector_identity`, `drift_error_bound` | Checked, hyp.: existence of the corrector `δ` (Poisson equation for `Q`), and the analytic estimates of the proof: the split `τ_tr = Qψ + r′` (`hsplit`) and the bounds on `r′`, `ψ′`, `ψ` (`hr`, `hψ'b`, `hψb`). Lean proves the modified-error energy argument |
| **Prop 4.5** moment-corrected dissipation | `moment_corrected_admissible`, `moment_corrected_first_moment` | Partial: (i) and (iii) for a given correction `ε` (time step `τ∑γ ≤ 1`; (i) requires `s > 0` strictly, so directions with `a_d = 0` are not covered); the existence of `ε` under the cone condition and part (ii) (see gap 3) are not formalized |
| **Lemma 5.1** skew central part | `conv_transpose_odd/even`, `odd_of_anticommute`, `even_of_commute`, `skew_qf_zero`, `lattice_contraction_iff` | Partial: the energy argument and the "iff" are checked; the reflection identity of the scheme (that the fits are reflection-equivariant) is a hypothesis |
| **Thm 5.2(ii)** nearest neighbour, any `D` | `k2_nearest_neighbour`, `k2_nearest_neighbour_D` | Partial: the trigonometric identity `cos θ − 1 + ½ sin²θ = −½(1 − cos θ)²` and its sum over `d` are checked; the step from the `K = 2` scheme to its symbol `eq:rek2`, the main step of the proof, is not formalized |
| **Thm 5.2(i)** `K = 2`, 1-D lattice | `k2_symbol_mu_form`, `k2_mu_form_eq`, `E_eq_cheb`, `k2_lattice_1d`, `k2_lattice_1d_symbol`, `E12_closed_form`, `P11_P21_nonneg` | Partial: from the symbol `eq:rek2` on, checked with `P_nm ≥ 0` on `[-1,1]` for `1 ≤ m ≤ n ≤ 9` as computer-assisted hypothesis (`P_11`, `P_21` proved); deriving `eq:rek2` from the scheme is not formalized |
| **Thm 6.1** Bloch reduction, `𝒦_Y` criterion | `bloch_bound_iff`, `bloch_stable_iff` | Partial: the DFT norm identity `eq:blochnorm`, `‖e^{tL_ℓ}‖ = max_θ ‖e^{tℓÂ(θ)}‖` (`hnorm`), which is the block diagonalisation that the paper proves; Lean proves the passage from it to the `𝒦_Y` criterion through the sampling sets |
| **Prop 6.3** sufficient condition | none | Not done (needs Kato perturbation theory) |
| **Cor 6.4** instability | `bloch_unstable` | Checked, hyp.: `‖e^{sM}‖ ≥ e^{sα(M)}`, continuity of the spectral abscissa, the DFT norm identity `eq:blochnorm` (`hnorm`) and the approximation hypothesis `happrox` |
| **Thm 7.3** smoothly deformed lattices | `dop_V_symmetrize`, `dop_weighted_bound`, `gaarding_transfer`, `deformed_energy`, `deformed_stability` | Partial: Lax–Nirenberg (Thm 7.2, cited, `hLN`), the form of `L` (`hL`) and the `O(h)` bounds of Steps 1 and 2 of the proof (`hc`, `hratio`, `hP₁`), which the paper proves, are hypotheses; Lean proves the energy argument from them |
| **Cor 7.4** order two in 1-D | none | Not done: no composition of `k2_lattice_1d_symbol` and `deformed_stability` exists in Lean, and it cannot be made as stated, because `deformed_stability` needs the Lax–Nirenberg hypothesis `hLN`, which `k2_lattice_1d_symbol` does not provide; the aligned-orientation sign argument is not done either |
| **Lemma 8.1** local squares | `squares_expand`, `local_squares`, `localSq_const` | Partial: the Fejér–Riesz factor `b_g` (cited) and the Toeplitz identification of the quadratic form (`hfr`) are hypotheses; the Lipschitz dependence of `b_g` on `g`, part of the conclusion, is not stated in Lean |
| **Lemma 8.2** deformed lattices, local form | `deformed_squares` | Partial: the banded-matrix estimate (`banded_qf_le`) is checked; the entrywise `O(h)` bound `hR`, which is the content of the lemma, is a hypothesis |
| **Lemma 8.4** support | `support_distances` | Partial: the distance bookkeeping is checked (the assumption `d ≤ 4κ` is not needed); the claim that `E_τ(W)` vanishes outside `Z′×Z′` is not formalized |
| **Prop 8.6** residual cannot be zero | `nsd_kernel`, `residual_zero_left_null` | Partial: a zero residual forces a left null vector; the attainment of the SDP optimum (compactness), used to conclude `res > 0`, is not formalized |
| **Thm 8.7** lattices with defects | `separation_disjoint`, `superposition_qf`, `defects_energy`, `defects_stability`, `defects_norm_equiv` | Partial: the SDP certificates `W_{τ,g}` with residuals, and the analytic steps of the proof, are hypotheses: the decomposition `R = Σ_A R_A + R_0` with disjoint blocks, `R_A = E_{τ_A}(W_{τ_A,g(z_A)}) + O(h)` and `R_0 = O(h)` (`hR`, `hB`, `hWc` of `defects_energy`, `hR₀` of `superposition_qf`). Lean proves `separation_disjoint` and the energy/Grönwall step, but `hdisj` of the energy theorem is not linked to `separation_disjoint`. Constant in `eq:defectsbound`: see gap 1 |
| **Cor 8.8(i)** zone radius, bounded rate | `zone_radius_choice`, `defects_rate_bounded` | Partial: the choice of `ϱ_h` and the bounded rate under the exponential-decay hypothesis `res(ϱ) ≤ C₀e^{-cϱ}` (numerical, not verifiable by computation) are checked; the step `R_A = E_τ(W_τ)`, `R_0 = 0`, `C = 0` for `φ = id` and the `log²(1/h)` bound for deformed lattices are not formalized |
| **Prop 9.1** numerical abscissa lower bound | `defect_inner`, `numerical_abscissa_lower_bound` | Checked (with a simpler test vector, see gap 4) |
| **Prop 9.2(i), (ii)** nearest-neighbour `K = 2` | `nn_interp_slope`, `nn_rusanov_upwind`, `nn_slope_normal_eq`, `nn_conservation`, `nn_energy_identity`, `nn_Q_second_form` | Partial: (ii) checked; for (i) `nnRhs` is defined directly in the final form `eq:fv` rather than composed from the separate lemmas, the second conjunct of `nn_interp_slope` is the tautology `(a/2)(1/a) = ½`, and the antisymmetry `V_i c_{i,i+1} = −V_{i+1} c_{i+1,i}` is not stated |
| **Prop 9.2(iii)** sign of `𝒬` | `nn_uniform_nonneg`, `nn_Q_indefinite`, `two_periodic_det_neg` | Partial: uniform case, indefiniteness on `ℝ^N`, and the 2-periodic determinant are checked; the Bloch reduction to the `2×2` form and the `N ≤ 64` computations are not done |
| **Prop 9.3** parity | `cos_sin_taylor`, `cos_taylor_bound`, `parity_expansion`, `local_symbol_re`, `parity_remainder` | Partial: the expansion is checked under the proposition's working hypothesis `hann` (annihilation of even monomials); the consequences (i) and (ii), including the `K = 2` diffusion coefficient `D_i`, are not stated in Lean |

Generic tools (Energy.lean): `energy_bound`, `energy_bound_sqrt`, `energy_forced`,
`linear_ode_exists`, `banded_qf_le`.

Summary: of the 30 rows, **2 are checked**, **7 are checked under explicit hypotheses**,
**19 are partial**, and **2 are not done** (Prop 6.3, Cor 7.4). The hypotheses of the
"Checked, hyp." rows are computer-assisted or cited inputs, and for Thms 3.1 and 4.4, Prop 3.3,
Prop 4.3 and Cor 6.4 also the proof steps of the paper listed in the row. A row is "Partial"
whenever a main scheme-specific step of the paper's proof, or part of its conclusion, is not
proved in Lean.

(Labels corrected on 4 Nov 2026 after an independent review, earlier count 14 / 10 / 5 / 1,
and again on 5 Nov 2026 after the A2 review of commit a6edcc9, count before 6 / 10 / 13 / 1.
No Lean statement changed; neither review found a false or vacuous statement.)

## Gaps found in the paper (fixed in `stability_combined.tex`, 29 Oct 2026)

1. **Thm 8.7, constant in `eq:defectsbound`.** From `eq:defects`
   (`min(c_W,1) g₋h ≤ W_h ≤ max(C_W,1) g₊h`) and `g₋h ≤ V ≤ g₊h`, the norm-equivalence
   constant for `‖·‖_V` is `(g₊/g₋) sqrt(max(C_W,1)/min(c_W,1))` (`defects_norm_equiv`).
   The paper had `sqrt(max(C_W,1) g₊ / (min(c_W,1) g₋))`, the constant for the unweighted
   norm `h|·|²`. **Fixed**: the constant in `eq:defectsbound` is corrected and the last
   sentence of the proof now shows the two norm comparisons. The rate and the stability
   conclusion are unchanged.
2. **Lemma 8.4.** The proof used `d ≤ 4κ`, which is not an assumption anywhere and is not
   needed: the sites `j, …, j+d` of a square through `y` lie within `d` of `y`, so they are
   outside `Z` (`support_distances`). **Fixed**: the proof now argues this way. The corrected
   separation `σ = 2ϱ + 2d + 12κ + 2` makes the blocks `Z''_A` disjoint (`separation_disjoint`).
3. **Prop 4.5(ii)** said that Thm 3.1 and Thm 4.1 hold for the corrected dissipation, but not
   under which time step. The uncorrected conditions are not enough, since `γ ≥ s|c|`.
   **Fixed**: (ii) now states (M6) as `2τ∑_{j,d}γ^d_{ij} ≤ 1` and the condition of Thm 4.1(iv)
   for the entries `q_{ij} = ∑_d(γ^d_{ij} - a_d c^{(d)}_{ij})`.
4. **Prop 9.1.** The step `η ≤ ½` used `‖g‖_H ≤ ‖L‖_H` without saying why. **Fixed**: the proof
   now notes `‖g‖_H = ‖L^{*_H}e‖_H ≤ ‖L^{*_H}‖_H = ‖L‖_H`. (Lean uses the test vector
   `U = 1 + d/(2Λ)`, which has `⟨1, d⟩_H = 0` and gives the same bound directly.)

No error was found in the other proofs. All the algebraic identities (energy identities,
summations by parts, the `μ`-form and `E_nm` expansion of Thm 5.2, the exact energy identity
of Prop 9.2, the parity expansion) check exactly as written.

## Files

* `MeshfreeStability/Imports.lean`: Mathlib imports
* `MeshfreeStability/Energy.lean`: energy method, forced systems, matrix exponential, banded bounds
* `MeshfreeStability/Nonlinear.lean`: Section 3
* `MeshfreeStability/Markov.lean`: Section 4
* `MeshfreeStability/Lattice.lean`: Section 5
* `MeshfreeStability/Bloch.lean`: Section 6
* `MeshfreeStability/Deformed.lean`: Section 7
* `MeshfreeStability/Defects.lean`: Section 8
* `MeshfreeStability/Limits.lean`: Section 9
* `MeshfreeStability/AxiomCheck.lean`: `#print axioms` for 77 main results
