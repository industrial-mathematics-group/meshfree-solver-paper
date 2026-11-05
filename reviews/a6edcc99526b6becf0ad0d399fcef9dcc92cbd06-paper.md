# Independent review of `paper/` and `addendum/` at a6edcc9 (pass 1)

- Commit reviewed: `a6edcc99526b6becf0ad0d399fcef9dcc92cbd06` (branch `main`)
- Date: 2026-11-05
- Reviewer: Claude Opus 5.5 (Anthropic), a new Claude Code session. It had no access to the generating
  conversations or notes and read only the repository. Two helper agents in the same session (also
  Claude Opus 5.5) did parts of the checks: one re-derived the addendum and compared it with Lean, the
  other reproduced numbers from scripts and run reports. I spot-checked their main findings myself
  (see "How the findings were confirmed").
- Scope: `paper/` (main_light.tex, refs.bib, .bbl, PDF, figures) and `addendum/` (math_addendum.tex,
  bib files, PDF, TikZ figure). Scripts in `scripts/`, `fv_reference/` and `results/` were run or read
  only as far as the paper and the addendum depend on them. `lean/` was compared statement by statement
  with the addendum but not built, because Lean/Lake is not installed in this environment.
- Extra check scripts: `reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-paper/`.

## Summary

Both documents build cleanly with `latexmk -pdf`: no undefined references or citations, and the
regenerated `.bbl` is identical to the committed one. The text of the committed PDFs matches the
sources. The mathematics of the paper and of the addendum checks out; no proof is broken.

Almost every number in the paper reproduces from the scripts and from the HyperCloudCore 0.7.8 run
reports. The exceptions:

1. **Error:** the wave positions in the Mach 3 step table (bow shock, Mach stem) do not match the
   shipped figure.
2. **Error:** the figure-measurement scripts do not run on the shipped figures.
3. **Error:** the addendum abstract says "four interface rules", but there are now three.
4. **Should-fix:** several statements are internally inconsistent or lack a source in the repo.

The HyperCloudCore simulations themselves (Julia) could not be rerun here. Those numbers are checked
only against the shipped reports and configs.

## Findings

### Errors

E1. **`paper/main_light.tex:776–779`, Table `tab:steppos`, and `:784`.** The bow shock and Mach stem
positions do not match `paper/figures/mach3_density_078.jpg`. I ran the repo's own algorithm
(`scripts/figure_measurements/steppos.py`), corrected only for the panel frames of the 078 figure; see
`steppos_078_frames.py`. The frames are (109–821, 996–1707, 1882–2594, 2769–3480) × (112–2249) px, with
the same scale in x and y.

| run | bow shock, y=0.05 | Mach stem, y=0.95 | reflection on step, y=0.215 |
|---|---|---|---|
| RK3MUSCL3(EPD1,MLS3) | 0.302 (paper 0.29) | 0.583 (0.57) | 1.314 (1.31) |
| RK3MUSCL3(EPD2,MLS3) | 0.305 (0.29) | 0.585 (0.57) | 1.292 (1.28) |
| RK4SSPMUSCL4(EPD1,MLS4) | 0.306 (0.29) | 0.585 (0.57) | 1.262 (1.25) |
| RK4SSPMUSCL4(EPD2,MLS4) | 0.305 (0.29) | 0.585 (0.57) | 1.238 (1.23) |

- The triple-point routine of the same script gives the stem at 0.577–0.580 and the triple point at
  y ≈ 0.735 (the paper says ≈ 0.75).
- The bow shock and stem differ from the paper by 0.013–0.017, which is more than the stated accuracy
  of 0.01. The reflection positions agree.
- As a calibration check, the same approach gives the exact Riemann-problem shocks (0.372/0.300 against
  0.373/0.301) and the DMR incident shock (3.047 against 3.053).
- Consequence: the sentence at `:784`, "our values, 0.29 and 0.57, lie about 0.02 upstream" of the
  FV reference (0.31; 0.62/0.60/0.59), should read "about 0.30–0.31 and 0.58, within about 0.01 of the
  reference".
- Most likely the old values were read from an earlier version of the figure.

E2. **`scripts/figure_measurements/{steppos,dmrpos,clainpos2}.py`.** All three stop with
`IndexError: boolean index did not match`. Their panel pixel coordinates are hard-coded for an older,
larger image layout (rows up to about 5828 px), while the `*_078.jpg` figures are 2400 px wide. As
shipped, none of the figure-read positions in `:736`, `:756` and `:776–784` can be reproduced. The
frames should be detected (the scripts already print them) or updated.

E3. **`addendum/math_addendum.tex:71` (abstract).** The abstract says "with four interface rules", but
the addendum defines three (EPD0/1/2). StrictEPD0 was removed (App. A, item 10, `:649`), and the paper
says three.

### Should-fix

S1. **`paper/main_light.tex:263` vs `:418` and `:686`.** Section 3.5 says the aligned orientation is used
"on all edges of the first-order scheme K=1". The experiments, however, run RK2MUSCL1 with the plain
geometric Rusanov flux "as a baseline", and `tab:options` makes the flux a separate setting. Say that
K=1 uses the aligned flux *when the AlignedRusanov flux is selected*, or that this is the default and the
baseline overrides it.

S2. **`paper/main_light.tex:394`.** The time step uses "derivative weights of the full-order degree
(capped at four, three in 3-D)". This contradicts `:394` itself ("the frozen mode with k_div=2 takes as
many steps as the second-order scheme for every K"), and the step counts in the reports agree with the
latter: on the step, k_div=2 takes 13.5–13.7k steps against 13.1k for K=2, and the vortex runs take
4014/4037 steps. The degree evidently follows q(k_div). Also, "capped at four" sits oddly with odd
derivative degrees 1, 3, 5. Say which degree is used.

S3. **`paper/main_light.tex:620` vs `:246`.** The paper explains the flat K=5 defects by stencils with
"fewer than 1.5·6 = 9 neighbours" at θ=0.4, κ=5.5 in 1-D. With offsets in [−0.4h, 0.4h], a particle can
drop below 9 neighbours only by losing both ±5h neighbours. That needs δ₅ − δᵢ > 0.5h and
δᵢ − δ₋₅ > 0.5h at the same time, which is impossible.
- Monte Carlo on 2·10⁵ particles (`nb.py`) gives a minimum of exactly 9. About 10% of particles have
  9 neighbours.
- So the explanation holds only if the code's safeguard is strict (more than 1.5× the unknowns), while
  `:246` says "at least 1.5 times".
- Under a strict rule, `:246` "k=5 needs about κ≥5.5 in one dimension" is borderline at θ=0.4. It is
  fine at θ=0.2, where the minimum is 10.
- Check the code and fix either the rule or the explanation.

S4. **`paper/main_light.tex:248`.** "Both [modes] coincide as long as no order is lowered" holds only if
q(k_div) = q(K). For example, k_div=2 with K=4 uses degree-one weights even with no order lowered,
which is the point of `:273`. The addendum says it correctly ("coincide for K≤2", `:286`).

S5. **`paper/main_light.tex:528–534`, Table `tab:vortex` (L² errors).** No file in the repo contains
these errors. `rerun-078-results.txt` and `rerun-078-tables.md` list only the minimum density, mass and
steps of the vortex runs. The orders recomputed from the tabulated errors agree to rounding (0.78/0.79,
7.67/7.68, 2.37/2.36), but the errors themselves cannot be verified. Add them to the reports.

S6. **Other numbers without a source in the repo.**
- `:559`: "π₀=10⁻² at N=100 with k_div=2". No such run is in results.
- `:686`: "All 60 runs". The enumeration in the text gives 19 runs per problem, i.e. 57. The 60 rows of
  `rerun-078-tables.md` include the 3 `clainshock_outflow` runs (transmissive boundaries, `:736`). Say
  "57 runs (60 with the transmissive Riemann runs)".
- There are no configs for the transmissive Riemann runs or for the coupled MUSCL4 DMR runs at 960×300.

S7. **Addendum, Prop 5.7 (`:478–486`) and Thm 6.3 (`:583–590`).** Both import "the hypotheses of
Prop 5.2 on 𝒢 and the fluxes". The condition s_{ij,d} > 0 wherever c ≠ 0 is, however, stated in
Prop 5.2 as a per-particle hypothesis (`:411`), and the proofs divide by s. Prop 5.7 should state that
λ_d > 0 on 𝒢; the Lean version has it as `hlam`. This is automatic for Euler, but `:90` claims every
hypothesis used is stated.

S8. **Addendum, Remark 1.2 (`:103`) says more is "checked in full" than the Lean shows.**
- Lemma 3.7(iii): the README says Lean checks only the value 17/5 ≠ 0, not that the stencil is
  unisolvent and centrally symmetric.
- Prop 5.2 / Cor 5.3: Lean assumes s > 0 for all j, d (`hspos`), and `aligned_update_admissible` takes
  the zero row sums as a hypothesis.
- Thm 6.3: Lean takes the Shu–Osher stage relation (`hSO`) as a hypothesis, and its `hone` requires
  order-one admissibility for every order distribution, which is stronger than (H4).

The remark should list these restrictions as it already does for Prop 4.3 and Cor 3.8. The statements
were compared, not built. No `sorry`, `admit`, `axiom` or `native_decide` occurs in
`lean/MeshfreeAddendum/*.lean`.

S9. **Addendum §6 (`:497–599`), notation.**
- K is both the design order and the RK stage slopes K_ℓ.
- k is both the checkpoint index and the orders k_i ("at every checkpoint k, every particle i with
  k_i=1").
- C (the set of lowered particles) sits next to 𝒞 (the SSP coefficient).

The paper uses ℓ, R_ℓ and Λ. Align the addendum with that.

S10. **`scripts/make_epd_figure_light.py:15` and `make_epd_figure_addendum.py:15`.** Both write to
`<repo>/figures/…`, which does not exist, so they fail with `FileNotFoundError` and never update the
files the documents load (`paper/figures/`, `addendum/figures/`). With the paths corrected, the output
is byte-identical to the committed figures.

### Minor

- `paper/main_light.tex:332`: "fails for 40–44% of the degree-three weights even on lattices". The
  lattice value is 40% and 44% is the perturbed value. Write "40% on lattices, 44% on perturbed clouds".
- `:512`: "5 to 30 times smaller" holds in 2-D (4.9–31.7). In 1-D, K=4 gives 42×; say "in two
  dimensions".
- `:686`, rounding:
  - "by up to 38%" is 38.8%;
  - "min p ≥ 0.25 for every K": K=2 EPD2 is 0.2497;
  - "agree to within 4%": 0.2785 vs 0.2898 is 4.1%.
- `:330`: the scalar maximum-principle bound needs s ≥ |f'| on the interval between U_i and U_j
  (or a convex flux), not only at the two end states.
- `:285`: "Together with the closure … the update would then be the FV-type update
  V_i dU_i/dt = −Σ S_ij·F*_ij". That form holds by definition. What antisymmetry adds is that it is a
  conservative FV update. Wording only.
- `:418` vs `:824`: the FV reference uses mirror cells at walls, not the nearest-donor ghosts of the
  meshfree code, so "the same boundary conditions" means the same types.
- Some numbers are not printed by any shipped script; they were reproduced by modified scripts:
  - equal-volume defects 5.7/16.7/72.9% (`:563` says 72.8%);
  - no-sweep defects 6.2/16.9% (`:861`);
  - "most negative ≈ half the mean" (0.47);
  - λΔt/h ≈ 0.32/0.11 CFL.
- The same-sign-pair row of `tab:stencils` is computed on 48×48, not on the 300×300 of the caption. On
  300×300 it gives 5.02/18.75/0.39/4.71%, the same after rounding.
- `scripts/fallback_positivity.py` reports 8.5% failures for degree-three weights with the geometric
  orientation, and `aligned_flux_diagnostics.py` reports 9.0%, which the paper quotes. They use the RNG
  differently. Their docstrings cite "(5.5)" and "Sec. 5.3", which are stale numbers.
- `results/reports/RUNS.md` says PDEStudioCore 0.4.2, while the paper and the CSVs say PDEStudio 0.4.5.
- `fv_reference/tst2.py` needs `dmr_240_l1_f0_front.txt`, which is not shipped.
- `results/configs/dmr_*_source_1.jl` contains stale settings (δ=0, classical RK4). The CSVs, which hold
  what was actually run, use RK4SSP and δ=10⁻⁴.
- Addendum:
  - `:616`: "k_div=K≥3 uses degree-three weights" holds only for K ∈ {3,4}.
  - `:650`: "both drafts", but only one draft is cited.
  - `:171`: B in "ε tr(N)/B" is undefined.
  - `:182`: 𝒟_i is defined but never used.
  - The sound speed c clashes with the weights c_ij (the paper has the same clash).
  - Lemma 6.1 should allow a different operator per stage, as its proof and the Lean version do.
  - `:311–315`: "strictly opposite signs are required" is sufficient, not necessary.
  - `:65`: the date (28 Oct) predates the fixes of 3–4 Nov.
- `lean/MeshfreeAddendum/AxiomCheck.lean:53` refers to `ReviewCompositions.lean`, which does not exist.

## Verified without problems

**Paper, mathematics**

- Scheme and zero row sums.
- Factor two.
- q(k) and Table `tab:degrees`, including the numbers of unknowns.
- Neighbour counts: 20 at κ=2.5, 96 at κ=5.5, 36 ≥ 32 at κ=3.2 in 2-D, and 10 at κ=5 in 1-D.
- Exactness argument.
- Lattice order argument.
- Balance law `eq:balance`, re-derived including the definitions of d and e and |e| ≤ |d| for both
  orientations.
- Positivity rearrangement `eq:convex` and the CFL condition.
- Lax–Friedrichs states.
- MOOD hop counts (1 hop, 2 for EPD2).
- SSPRK(5,4): C = 1.508 and the canonical final update 0.238 Uⁿ + 0.287 W₂ + 0.134 W₄ + 0.341 W₅ exactly
  (`ssp.py`).
- Burgers t* = ½e^{1/2} and the factor 2.5, periodic error 2·10⁻⁹.
- Vortex minimum density 0.4938.
- Riemann Configuration 3 shock speeds −0.663/−0.422 and positions 0.301/0.373.
- DMR shock line, top intersection 3.053.
- Particle counts in `tab:setup`.
- δ range 1.6·10⁻¹⁰ to 1.1·10⁻⁹.
- Shock-test floor −h/(2m) = −1.98·10⁻⁴.

**Paper, numbers**

- `tab:stencils`: every cell reproduced by `scripts/stencil_diagnostics.py`. This includes 4%/19%,
  3.2%, 5%/19% (0.4%/4.7%), 2.7× and 73%.
- Δt/h ≈ 0.15 and 0.06 at κ=5.5 (own lattice computation and step counts).
- `tab:convergence`: all rows recomputed from `rerun-078-results.txt`. This includes the means of the
  last three steps, the perturbed ratios, the κ=2.5 rows, "at most 6.3%" and "1.1e-7 vs 1.4e-6".
- `tab:vortex_min`: all 30 entries, plus the CPU/GPU and mass statements.
- `tab:euler2d`: all entries, plus the coupled-mode masses, the 0.25% statement, the step counts and the
  transmissive-boundary masses.
- `tab:sod`: all entries, plus the text ratios and 132 runs.
- `tab:mass_shock` and `tab:mass_2d`: all entries, rates, and the θ/κ/α sensitivities.
- The values read from the figure PDFs (L² ratios 4.9/8.5/5.0/19; range 8.6·10⁻⁴–2.3·10⁻³) are
  confirmed from the vector data.
- Configs agree with the stated κ, θ, CFL, steppers, resolutions, final times, zoom windows and methods.

**FV reference**

- `rh.py` and `tst.py` reproduce the exact relations.
- Coarse runs of `fv.py` (step 40, stepfix 40, dmr 120) reproduce the values in
  `reference_solutions.md`.
- The finer FV runs were not repeated (too expensive here).

**Addendum**

- All proofs were re-derived:
  - Lemmas 3.3, 3.5, 3.7, Cor 3.8;
  - Lemma 4.1, Props 4.2–4.4;
  - Props 5.2, 5.6, 5.7, Cor 5.3;
  - Lemma 6.1, Thm 6.3, Cor 6.4, Remark 6.5.
- The Lemma 5.1 identity was checked with sympy (`chk.py`).
- A 1-D lattice check of Prop 4.3 (`lat.py`) gives truncation orders 1, 2, 2, 3, 4 for
  (k,q) = (1,1), (2,1), (3,2), (3,3), (4,3).
- SSP coefficients and Table 1 are reproduced to four digits.
- The notation shared with the paper (scheme, aligned rule, CFL, EPD rules, balance law, q(k), 1.5×
  safeguard, Δt formula) is identical.
- The TikZ figure is byte-identical to the script output.
- All 17 cited keys exist, and the entries checked look correct.

## How the findings were confirmed

- E1, E2, S3, S5: re-checked by me (own frame detection and measurement, Monte Carlo, grep of the
  reports).
- E3, S7, S10: checked in the sources.
- The other findings come from one helper. I checked them for plausibility but did not repeat each one.

## Declaration levels I believe are correct

The Human-Review level is left to Pascal (TODO).

| Path | G | A | Remarks |
|---|---|---|---|
| `paper/**` (main_light.tex, .bbl, .pdf, refs.bib, figures) | G2 (G3 declared) | A2 with this review | The paper's own AI declaration (`:890`) says Opus 5.5 drafted substantial parts that the authors revised, which reads as AI-generated under human direction (G2). G3 holds only if the drafting was autonomous. The images are plots of executed code. Same model family as the generator (Opus 5.5), so A2, not A3. Back to A1 once E1/S1–S6 are fixed until re-reviewed. |
| `addendum/**` | G3 | A2 with this review | Generated with Claude Fable 5.1 in Claude Code per `:655`. The reviewer is a different model (Opus 5.5), but capability parity with Fable 5.1 is not established, and Lean was not built. So A2, not A3. |

Before this review no review file existed in `reviews/`, so A1 (as declared) was the correct level for
both. The "independent review of 3 Nov 2026" in the commit history was never committed. The paper's
declaration (`:890`) says independent sessions "rebuilt the Lean formalization". This review could not
confirm that, because Lean is not installed here.
