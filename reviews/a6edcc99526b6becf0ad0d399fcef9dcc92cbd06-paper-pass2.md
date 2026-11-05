# Independent review (pass 2): paper/ and addendum/

- Commit reviewed: `a6edcc99526b6becf0ad0d399fcef9dcc92cbd06`
- Date: 2026-11-05
- Reviewer: Claude Opus 5.5 (Anthropic). This was a new session with no access to the generating conversations or to earlier review files. The work was split across three sub-agents: addendum math + Lean, paper math + numbers, and reproducibility. The findings marked "confirmed" were re-checked by the lead session.
- Scope: `paper/main_light.tex`, `paper/figures/*`, `paper/refs.bib`, `addendum/math_addendum.tex`, `addendum/figures/*`. The review also covers how these files match `lean/MeshfreeAddendum/`, `lean/README.md`, `scripts/`, `fv_reference/` and `results/`.
- Check code and outputs: `reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-paper-pass2/`.

## What was and was not run

| Check | Status |
|---|---|
| `scripts/stencil_diagnostics.py`, `aligned_flux_diagnostics.py`, `fallback_positivity.py`, `make_epd_figure*.py` | Ran (outputs redirected) |
| `scripts/figure_measurements/*.py` | All fail on the current JPGs (see P3). Rerun with corrected pixel boxes (`repro/adapted/`) |
| `fv_reference/rh.py`, `tst.py` | Ran and match |
| `fv_reference/tst2.py` | Crashes on a missing data file after the exact part |
| `fv_reference/fv.py` | `step 40`, `stepfix 40` and `dmr 120` reproduce the coarse columns of `reference_solutions.md` exactly |
| Recompute convergence orders, `tab:convergence`, `tab:mass_shock`, `tab:euler2d`, `tab:vortex*`, `tab:sod` from `results/reports` | Done, all match except where listed |
| SSPRK(5,4) Shu–Osher form, 𝒞 = 1.508180, the −0.0208 stage-value coefficient, canonical forms of FE/RK2/RK3, the parity counterexample 17/5 | Recomputed and correct |
| HyperCloudCore simulations (Julia) | **Not run** (not available) |
| Lean build / AxiomCheck | **Not run.** The elan install was refused in this environment, so only the Lean source was read |
| LaTeX compile of either PDF | **Not run** (no TeX installation) |

## Findings: paper (`paper/main_light.tex`)

**P1 (error, confirmed) — line 248.** The text says "Both coincide as long as no order is lowered" about the coupled and frozen modes. That is false whenever q(k_div) ≠ q(K). For example, MLS2 with K ≥ 3 uses degree 1 in frozen mode and degree 3 in coupled mode with no order lowered, which is why the step counts in `tab:vortex_min` differ (4037 vs 11800). The addendum correctly says "Both coincide for K ≤ 2" (math_addendum.tex:286).

**P2 (error, confirmed) — `tab:steppos`, lines 776–779, and the claim at line 784.** Measured on the current `mach3_density_078.jpg`, the bow shock is at 0.303–0.307 and the Mach stem at 0.584–0.587. The table gives 0.29 / 0.57, which is +0.015 off and beyond the stated ±0.01. The step reflections measure 1.315 / 1.291 / 1.263 / 1.239, against 1.31 / 1.28 / 1.25 / 1.23 in the table. Because of this, the statement that the runs lie "about 0.02 upstream" of the FV reference (0.31 / 0.59) no longer holds; they lie 0.003–0.007 upstream. The table was probably measured on an earlier version of the figure. The frame boxes used were found from the image's frame lines; the plot is 2138×712 px, which matches the 3×1 domain.

**P3 (reproducibility, confirmed).** All three `scripts/figure_measurements/*.py` scripts fail with an IndexError. Their hard-coded pixel boxes belong to an older image layout (about 2959 px wide, rows up to 5828), while the current JPGs are 2400 px wide. With corrected boxes:
- Riemann: positions match.
- DMR: incident shock 3.037 (exact value 3.036) ✓, and the K = 3/4 stem 2.74–2.76 ✓.
- DMR VK stem foot: 2.785, against "≈2.80" in the text (line 758). This is minor.

**P4 (imprecision) — line 686, minimum pressures.** The text says the lowest pressures occur on the step with k_div = K and EPD1 (4.8e-3 for K = 3, 3.4e-2 for K = 4). Only 4.8e-3 is the global minimum. Several runs are below 3.4e-2: the coupled MUSCL3/EPD1 run on the step (0.014) and all Riemann runs (0.018–0.029).

**P5 (imprecision) — line 686, step counts.** The text says these runs take "as many time steps as the second-order scheme (13.5–13.7×10³ … compared with 13.1×10³ for RK2MUSCL1)". But the comparison value given is for the first-order run. RK2MUSCL2 takes 13511–13555 steps.

**P6 (cosmetic) — line 686, other numbers.**
- "Up to 38%" is 38.8% (0.01775/0.029), so it should read 39%.
- "agree to within 4%" is 4.06% for the K = 4 minimum pressure on the step.
- "All 60 runs" counts the 3 transmissive Riemann runs from line 736, but the configuration list in the same sentence gives 57.

**P7 (imprecision) — line 394.** ĉ is described as weights "of the full-order degree". The step counts show that the time step uses q(k_div) in frozen mode, and the following sentence relies on that. It should say "the degree in use".

**P8 (imprecision) — Table `tab:stencils`, rows 879–880, and line 263.** The values for pairs with c_ij·c_ji > 0 (5.0% / 19%, 0.4% / 4.7%) are correct for the 300×300 cloud in the caption; an independent recomputation gave 5.02 / 18.75 / 0.39 / 4.71. However, no shipped script prints them: `aligned_flux_diagnostics.py` runs a 48×48 cloud only. The Monte Carlo statement (9% inadmissible, line 332) comes from that 48×48 cloud, and the text should say so.

**P9 (imprecision) — Monte Carlo scripts disagree.** `aligned_flux_diagnostics.py` gives 1797/20000 = 9.0%, but `fallback_positivity.py` gives 1701/20000 = 8.5%, because one reuses an RNG stream and the other reseeds. Both are deterministic. The paper's 9% comes from the first script; the second should be aligned or the difference noted. The docstring of `fallback_positivity_lib.py` is a stale copy.

**P10 (imprecision) — line 559.** "Over the whole stencil of radius 2.5h the curvature … decays by a factor of about e³" depends on the resolution and radius. It holds only roughly near N = 100 at r ≈ 3, not for the N ≥ 200 the argument concerns.

**P11 (imprecision) — lines 410 and 512.** "5 to 30 times smaller" holds at the finest N (4.9–31.6) but not across all resolutions (2.9–56). It should say "at the finest resolution".

**P12 (declaration) — line 890.** The model attributions in the paper's AI declaration agree with AIDECL.toml: Opus 5.5 drafted the manuscript, and Fable 5.1 generated the addendum, Lean, stability note, scripts and FV code. But two parts are not covered by the current declarations and need Pascal's decision:
- **Review claim.** The paragraph says reviewers "rebuilt the Lean formalization" and that the authors "verified all content". At this commit, AIDECL.toml has H0 for `addendum/`, `lean/`, `scripts/`, `stability/` and `fv_reference/`, and this review could not rebuild Lean.
- **Unmentioned material.** `results/**` is also supplementary material (assisted by Opus 5.5 per AIDECL.toml) and is not mentioned.

**P13 (cosmetic) — supplementary metadata.**
- `results/reports/RUNS.md` says PDEStudioCore 0.4.2, while the paper and CSVs say 0.4.5.
- `euler_sod_components.csv` has `Grid_Ns=(330,)`, which is not in the sweep; the figure has about 200 points.
- The shock-mass-defect CSVs carry stale legend labels.
- The DMR and step config comments about "fixed order 3 and VK blow up" are stale.
- `make_epd_figure*.py` write to `<repo>/figures/`, which does not exist. Redirected, their output is byte-identical to both committed TikZ files.

## Findings: addendum (`addendum/math_addendum.tex`)

**A1 (error, confirmed) — line 71 (abstract).** The abstract says "the per-particle MOOD procedure with four interface rules". The body has three (EPD0, EPD1, EPD2, eq:epd), and App. A item 10 says StrictEPD0 was removed.

**A2 (imprecision) — line 617, rem:mood(iv).** "If every W_{j,i} satisfies (eq:dmp) with δ = 0": eq:dmp is the condition for flagging a state. It should read "is not flagged by (eq:dmp) with δ = 0", i.e. W_{j,i} ∈ [Y^min, Y^max]. The conclusion holds once this is fixed.

**A3 (imprecision) — line 103, rem:lean, lem:parity(iii).** rem:lean lists the parity counterexample as "checked in full". Lean only computes the sum 17/5; `lean/README.md` says the central symmetry and Π₂-unisolvency of the stencil are not proved. The docstring of `parity_fails_even'` in `MLS.lean` (around line 183) overstates this as well.

**A4 (imprecision) — line 103, rem:lean, thm:mood.** The remark says "one ingredient taken as a hypothesis" but then names two (prop:local and exact locality). In addition, `stagewise_mood_admissible` assumes:
- the Shu–Osher form of the stages (`hSO`, not derived from `shuOsher_form`);
- (H3) (`hghost`);
- `hone`, which requires an admissible substep for every order vector with k_i = 1. That is stronger than (H4).

`lean/README.md` describes this more accurately than rem:lean does.

**A5 (imprecision) — lines 71 and 535, rem:stagevalues.** The abstract claims that stage-value checking "suffices" for RK2 and RK3, but nothing proves it. The justification ("every W_j enters exactly one later row") is not the property needed. What is needed is that row k contains only Uⁿ and W_{k−1}; then prop:local gives admissibility at an order-one particle. That property does hold for FE, RK2 and RK3.

**A6 (cosmetic) — line 385.**
- "by (iii) on the remaining edges" is really the algebra of (i) with σ_ji = −σ_ij.
- The FV-type form V_i dU_i/dt = −Σ S_ij·F*_ij holds by the definition of S_ij. It is antisymmetry together with F*_ji = F*_ij that makes the form conservative.

**A7 (cosmetic) — line 603, cor:ssp.** The corollary invokes (H4), which is stated in terms of MOOD checkpoints, but claims the result "with or without MOOD". It should say "(eq:cflpos) with τ = Δt/𝒞 at every stage".

**A8 (cosmetic) — line 616.** "Frozen mode with k_div = K ≥ 3 uses degree-three weights" holds only for K ∈ {3, 4}, since q(5) = 5.

**A9 (cosmetic) — notation overloads.**
- s: stage count and wave speed.
- k: order, stage index and checkpoint (alg:mood uses both).
- c: sound speed and weights.
- d: direction and the defect d_{ij,d}.
- e: ones vector, unit vector and e_{ij,d}.
- γ: adiabatic exponent, a multi-index (line 239) and γ_d (line 349).
- R: support radius and the reflection R_d.

**A10 (cosmetic, Lean side).**
- `lean/MeshfreeAddendum/AxiomCheck.lean:53` cites `ReviewCompositions.lean`, which is not in the repo.
- `first_order_update_admissible` and `local_admissibility_order_one` assume s > 0 for all j, d and λ > 0 on all of 𝒢. Both are slightly stronger than the text but harmless for Euler.

### Checked and found correct (addendum)

- **Section 3:** lem:divfit (i)–(iii) with the S_θ scaling, lem:weightbound, lem:parity (i)–(iii), cor:derr, def:qk and rem:constant.
- **Section 4:** lem:symmetry, prop:exact, prop:lattice (parity of ψ_α, the reflection argument for γ_d = 0, the order count min(k, q+1)) and prop:conservation (i)–(iii).
- **Section 5:** lem:lfstates, with the internal-energy identity re-derived; prop:positivity, including the σ ≠ 0 clause; cor:aligned with the LED coefficients; prop:fallback; prop:local.
- **Section 6:** lem:canonical, the thm:mood induction, and exact locality (radius 1 for EPD0/1, 2 for EPD2).
- **SSPRK(5,4):** tab:ssprk54 to 4 digits, and the negative coefficient confirmed inside the Lean tolerance box.
- **Cross-references and citations:** all resolve.
- **Lean source:** contains no `sorry`, `admit`, `axiom` or `native_decide`. The hypotheses of `stagewise_mood_admissible` can be satisfied, so the theorem is not vacuous.
- **Figure:** the generator's output is byte-identical to the committed TikZ file, with red half-edge counts 4 / 8 / 32.

### Checked and found correct (paper)

- **Scheme and its properties:** scheme definition, dissipation coefficient, balance law, \|e\| ≤ \|d\|, eq:convex, and the CFL conditions, which match the addendum's Prop. 5.2 / Cor. 5.3.
- **Agreement with the addendum:** EPD rules, Algorithm 1 and the SSP coefficients all match.
- **Tables:** every entry of tab:convergence (54 orders recomputed), tab:vortex, tab:vortex_min, tab:mass_shock, tab:mass_2d, tab:sod (as tabulated), tab:euler2d and tab:stencils (rerun).
- **Values in the text:**
  - Mass-defect range 8.6e-4 to 2.3e-3 for N ≥ 631, read from the figure data.
  - Relative-L² factors 4.9 / 5.0 / 8.5 / 19.
  - δ range, Δt/h ratios, t* = 0.824, the Burgers floor value −1.98e-4.
  - Rankine–Hugoniot (RH) speeds −0.663 / −0.422.
  - FV reference values.
- **Bibliography:** all 73 cited keys are present.

## Declaration levels I believe are correct for the reviewed files

| Path | G | A | Note |
|---|---|---|---|
| `paper/**` | G3 as declared (the paper's own statement, "drafted substantial parts … authors revised", reads like G2; Pascal decides) | **A2** (this review) | Falls back to A1 once P1–P11 are fixed, until reviewed again |
| `addendum/**` | G3 (generated by Fable 5.1) | **A2** (this review) | Not A3: the reviewer is a different model, but the Lean build could not be rerun here. Falls back to A1 after fixes |

Human-Review is left as TODO for Pascal. AIDECL.toml was not edited; declarations are consolidated in another thread.
