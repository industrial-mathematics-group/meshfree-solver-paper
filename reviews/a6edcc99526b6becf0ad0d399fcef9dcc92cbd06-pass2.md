# Independent review of `lean/` (pass 2) at a6edcc9

* Commit reviewed: `a6edcc99526b6becf0ad0d399fcef9dcc92cbd06` (main, 5 Nov 2026)
* Scope: everything under `lean/` (libraries `MeshfreeAddendum`, `MeshfreeStability`,
  `README.md`, `STABILITY.md`, Lake configuration), compared with
  `addendum/math_addendum.tex` (Sections 3 to 6, Remark 1.2) and
  `stability/stability_combined.tex` (Part I, Sections 3 to 9).
* Reviewer: Claude Opus 5.5 (Anthropic), a new session that saw only the repository. It did
  not see the generating conversations, the other review threads or earlier review files.
* Extra checks: `reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-pass2/`.

## Verdict

The formalization builds, uses no `sorry` and no non-standard axioms, and every Lean
statement I compared with the paper says what the README / STABILITY.md tables claim. I found
**no false, vacuous or silently weakened statement**. The findings below are about status
labels, one small missing case and the AI declaration. Recommended level for all of `lean/`:
**G3 · H TODO · A2**.

## 1. Build and axioms

* Toolchain `leanprover/lean4:v4.35.0` from the GitHub release, Mathlib `v4.35.0`
  (rev `56a00585`) compiled from source, because `cache.mathlib.org` is blocked here.
  `lake build`: **Build completed successfully (2894 jobs)**. Only linter warnings
  (unused variables, unreachable tactics) in the project files, no errors.
* `grep` for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`,
  `opaque`, `macro`, `elab`, `#eval` in the project sources: no hits outside comments.
* The project's own `AxiomCheck.lean` files: 42 + 77 results, all
  `[propext, Classical.choice, Quot.sound]`.
* `AllAxioms.lean` (this review) runs `#print axioms` on **all 230 theorems** of both libraries,
  not only the selected ones: every one depends on a subset of
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.

## 2. Statements against the papers

I read every definition and theorem statement and checked the following against the TeX.

**Addendum.**

| Paper | Lean | Check |
|---|---|---|
| Lem. 3.3 (i)–(iii) | `divWeight_reproduces`, `divWeight_sum_eq_zero`, `divWeight_dilate` | match; `divWeight` is eq. (3.2) with the exact inverse; dilation for any `θ ≠ 0` (paper `θ > 0`) |
| Lem. 3.5 | `divWeight_abs_le`, `sum_abs_le_of_abs_le` | match; `hCN` is `‖(Ñˢ)⁻¹‖₂ ≤ C_N`, `hCκ` is `|p̃_q(x/h)| ≤ C_κ`, `0 ≤ w ≤ 1` |
| Lem. 3.7 (i), (ii) | `divWeight_antisymm`, `divWeight_reproduces_succ_of_odd` | match |
| Lem. 3.7 (iii) | `parity_fails_even'` | value `17/5 = Σx⁴/Σx²` as in the proof; hypotheses of the counterexample now proved, see §3 |
| Cor. 3.8 | `derivative_error_le` | algebraic core, Taylor remainder as hypothesis (as labelled) |
| Def. 3.9 | `qdiv_*` | match |
| Lem. 4.1, Prop. 4.2 | `rusanov_swap`, …, `exactness_linear` | match; interface states as hypotheses (as labelled) |
| Prop. 4.3 | `lattice_flux_parity`, `lattice_flux_cancel` | only the algebraic steps (as labelled) |
| Prop. 4.4 (i)–(iii) | `conservation_balance`, `eDef_*`, `local_conservation` | match; ordered pairs with `½` equal unordered pairs by `bracket_symm` |
| Lem. 5.1, Prop. 5.2, Cor. 5.3 | `lf_state_admissible`, `first_order_update_admissible`, `aligned_update_admissible`, `scalar_led` | match; CFL `τΣ s|c| ≤ 1` (5.1) and `2τΣ s|c| ≤ 1` for LED as in the paper; (b) as `σc = |c|` as in the current text |
| Props. 5.6, 5.7 | `fallback_orders`, `fallback_all_order_one`, `epd0_*`, `local_admissibility_order_one(_epd)` | match; `s = max(λ(Y_i), λ(Y_j))` as in the statement; extra hypothesis `λ > 0` on `G`, which holds for Euler (`euler_prop57_hyps`, §3) |
| Lem. 6.1, RK1–RK3 | `shuOsher_form`, `rk*_canonical` | match (any `r ≠ 0`) |
| Rem. 6.2, Table 1 | `ssprk54_elimination`, `ssprk54_negative_coefficient` | match. I recomputed Table 1 from the Spiteri–Ruuth coefficients (`check_ssprk54.py`): `C = 1.50818`, all entries agree to 4 digits, the eliminated coefficients are `0.5172, 0.1627, 0.3409` and `−0.0208`, so the Lean hypotheses hold for the real method |
| Alg. 1, Thm. 6.3, Cor. 6.4 | `Checkpoint.run(_spec, _admissible)`, `stagewise_mood_admissible`, `ssp_order_one` | match the proof's induction; `hone` (Prop. 5.7 + (H4)), `hloc`, `hSO` are hypotheses (as labelled). `hone` quantifies over all order vectors with `k_i = 1`; this is equivalent to (H4) because the weights and speeds of an order-one particle do not depend on the other orders |

**Stability note, Part I.** Every row of STABILITY.md matches the Lean statement and the
paper, with the hypotheses listed there. I checked in particular: the DMP version of the
checkpoint (`dmp_checkpoint`, Thm 3.1 with (M4)–(M6)); `euler_l1_bounds(_defect)`; the Riemann
average identity and the convex-combination proof of Prop. 3.5; the sign and the pair form of
`global_entropy_balance` against eq. (3.6); the Markov results of Thm 4.1; the CFL conditions of
Prop. 4.5 (`τΣγ ≤ 1` for (i)); the `2P + (ε+ε′)t` bound of `drift_error_bound`; the `μ`-form
and `E_nm` identities of Thm 5.2; the constant `(g₊/g₋)√(max(C_W,1)/min(c_W,1))` of
`defects_norm_equiv`; the factor `9` of Prop. 9.1; `nnGamma`, `nnM` and `nnQ` against
eqs. (9.2), (9.3).

Non-vacuity of the computer-assisted hypothesis `hP` of `k2_lattice_1d`: `check_pnm.py` finds
`min P_nm ≥ −1e−30` on `[−1,1]` for `1 ≤ m ≤ n ≤ 9` (floating point) and `min P_{10,1} ≈ −0.67`,
consistent with the bound `κ < 10`.

## 3. Extra Lean checks (`NonVacuity.lean`, compiles, standard axioms)

* `parity_fails_even_full`: the counterexample stencil `±1, ±2` with unit weights **is**
  `Π_2`-unisolvent (`cex_unisolvent`, via a new converse `unisolvent_of_gram_isUnit`) and
  centrally symmetric (`cex_centrallySymmetric`, involution `Fin.revPerm`). This closes the gap
  that `lean/README.md` lists for Lemma 3.7(iii) and makes the addendum's claim in Remark 1.2
  ("checked in full, including the counterexample") literally true. Suggest moving these
  ~40 lines into `MLS.lean`.
* `euler_prop57_hyps`: `LFHyp` and `λ > 0` hold for Euler, so Prop. 5.7 / Thm 6.3 are not
  vacuous for the intended instance.
* `checkpoint_hyps_satisfiable`: `Checkpoint.Local` and `C ⊆ hood C` can hold together.

## 4. Findings

1. **STABILITY.md, Thm 4.1(iv) labelled "Checked", but the RK case is only stated for finite
   `p`.** `rk_contraction_p` takes `p : ℝ`, `1 ≤ p`; for `p = ∞` there is `euler_step_max`
   (forward Euler) but no Runge–Kutta statement. It follows in two lines from `ssp_stages`
   with `convex_Icc`; either add it or relabel the row "Partial". Minor.
2. **Addendum Remark 1.2 vs. README for Lemma 3.7(iii).** The remark says checked in full; the
   README says the counterexample's hypotheses are not proved. Resolved by §3; update the
   README row when the lemma is moved in. Minor.
3. **Abstractness of Thms 3.1 / 6.3 and Thm 6.1.** `Checkpoint.W` is not linked to `schemeOp`,
   and `bloch_*` work with arbitrary functions `N`, `g`. Both are stated honestly in the tables;
   readers should know that Thm 6.1 in Lean is the density/semicontinuity argument only. No
   change needed.
4. **Unused hypotheses** (linter): `scalar_led` does not use the zero row sums `ha0`;
   `bloch_bound_iff` does not use `hmult`; `lattice_contraction_iff` `hS` (Lattice.lean:95);
   `hτ` at Nonlinear.lean:400. These make the theorems stronger, not weaker. For `scalar_led`
   it shows that the LED property of the aligned first-order operator holds without zero row
   sums (the `F(U_i)` terms already cancel in `F* − F(U_i)`). Optional cleanup, plus ~20
   unused-tactic warnings.
5. **AI declaration of `lean/**`.** `AIDECL.toml` gives `Assisted-by = "Claude (Anthropic),
   claude-fable-5-1"`, but commit `824d923` (co-authored by Claude Opus 5.5) changed
   `Positivity.lean` (+43 lines, the composed `local_admissibility_order_one_epd`), `Time.lean`,
   `AxiomCheck.lean` and four stability files. Assisted-by should name both models. Because an
   Opus 5.5 session wrote part of `lean/`, this Opus 5.5 review counts as **A2, not A3**.
6. `reviews/**` is not yet in the `AIDECL.toml` exclude list (left to the consolidating thread,
   as instructed; `aidecl lint --strict` passes with the default `**` rule).

## 5. Recommended declarations

| Path | G | A | Notes |
|---|---|---|---|
| `lean/MeshfreeAddendum/**` | G3 | A2 | Assisted-by: Claude Fable 5.1, Claude Opus 5.5 |
| `lean/MeshfreeStability/**` | G3 | A2 | same |
| `lean/MeshfreeAddendum.lean`, `lean/MeshfreeStability.lean` | G3 | A2 | |
| `lean/README.md`, `lean/STABILITY.md` | G3 | A2 | fix finding 1 (and 2) |
| `lean/lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore` | G3 | A2 | build reproduced |

H stays TODO (set by Pascal). AI-Reviewed-by for A2:
`Claude Opus 5.5 (Anthropic), new session (reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-pass2.md)`.

## Reproduction

```
cd lean
lake build                                   # 2894 jobs
lake env lean ../reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-pass2/AllAxioms.lean
lake env lean ../reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-pass2/NonVacuity.lean
python3 ../reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-pass2/check_pnm.py
python3 ../reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-pass2/check_ssprk54.py
```
