# Code review, pass 2 (independent), commit a6edcc99526b6becf0ad0d399fcef9dcc92cbd06

- **Scope:** all code outside `lean/`: `scripts/` (including `figure_measurements/`), `fv_reference/`, `stability/scripts/` with `stability/data` and `stability/tables`, and `results/configs` and `results/reports`.
- **Reviewer:** Claude Opus 5.5 (Anthropic). This was a new session that did not see the generating chats, their notes or the earlier reviews in `reviews/`. `stability/scripts` was delegated to a sub-agent of the same session (same model, also without the generating context). I re-ran its main finding myself.
- **Level:** A2. The reviewer is the same model family that generated the code, so this is not A3.
- **Date:** 2026-11-05.
- **Environment:** Python 3.13, NumPy, SciPy, SymPy, Numba, matplotlib, Pillow, cvxpy (latest pip), 4 CPU cores. HyperCloud / HyperCloudCore are not available, so the Julia run configurations could not be executed.

Extra test code is in the folder of the same name, `reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-code-pass2/`:

| File | What it checks |
|---|---|
| `test_stencils.py` | MLS weights are exact on all monomials of degree ≤ q, on lattices and on perturbed clouds. Also checks neighbour symmetry, the Euler flux helpers, and that the aligned first-order update stays admissible. Passes. |
| `test_fv.py` | HLL/HLLC consistency. Runs a Sod shock tube along x and along y on n = 100, 200, 400 against the exact Riemann solution. Passes. |
| `test_defect_bloch_h.py`, `defect_bloch_fixed_h_sweep.py` (+ `.out`), `defect_bloch_kreiss_fixed_h.py` | Show the h bug in `ho_common.bloch_symbols` (finding S1). Usage: `python3 <file> stability/scripts [reviews/<folder>]`. |
| `test_bloch_aliasing.py` | Compares 3 and 5 supercell copies. They agree to 1e-14, so the supercell is not aliased. |
| `cmp_jsonl.py` | Record-matching diff of re-generated against committed `.jsonl` data. |

Run `test_stencils.py` and `test_fv.py` from the repository root. `test_fv.py` writes `.npz` files to the directory given by `OUT` (default: the current directory).

## Summary

| Path | Proposed G | Proposed A | Result |
|---|---|---|---|
| `scripts/stencil_diagnostics.py` | G3 | A2 | Table "Stencil diagnostics" reproduced exactly. One caption inconsistency (C3). |
| `scripts/fallback_positivity*.py`, `scripts/aligned_flux_diagnostics.py` | G3 | A2 | Every quoted number reproduced. The "9 %" is 8.5 % or 9.0 % depending on the script (C2). |
| `scripts/make_epd_figure*.py` | G3 | A2 | Output is byte-identical to the committed TikZ files, but the scripts crash on the output path (C1). |
| `scripts/figure_measurements/` | G3 | A1 | **Cannot be run on anything in the repository** (C4), so I could not review it beyond reading. Keep at A1. |
| `fv_reference/*.py` | G3 | A2 | Solver verified. Every value in `reference_solutions.md` that I re-ran is reproduced (DMR 1/120 and 1/240, step 1/40, 1/80 and 1/160, Riemann problem 400²). Minor issues F1 to F5. |
| `fv_reference/reference_solutions.md` | G3 | A2 | Two Riemann-problem triple points do not follow from `analyze.py` (F3). The fallback claim is imprecise (F4). |
| `stability/scripts/` + `stability/data`, `stability/tables` | G3 | A2 | Data and tables reproduce. **One major bug in 1-D merge/insert defect cells** (S1) and several text/data mismatches (S2 to S9). |
| `results/configs/` | G3 | A1 | Not executable here: HyperCloud is missing and the included base files are not shipped (R1). I only checked the parameters against the paper captions, and they agree. |
| `results/reports/` | G3 | A1 | Spot check only: the Sod table matches the paper digit for digit. The underlying runs cannot be repeated without HyperCloud. |

I can only judge the G level from style, history and the existing declarations. The code is uniformly terse and machine-like, and the commits are by Claude. Nothing contradicts the declared G3.

## Findings

Severity is **major** (a wrong number in a document, or a result that cannot be reproduced), **minor**, or **nit**.

### scripts/

**C1 (minor): `make_epd_figure.py:82`, `make_epd_figure_addendum.py:15` and `make_epd_figure_light.py:15` write to the wrong place and crash.**
- They write to `<repo>/figures/…`, which does not exist, so every run ends in `FileNotFoundError`.
- The figures they are meant to produce live in `paper/figures/epd_rules_light.tex` and `addendum/figures/epd_rules_addendum.tex`.
- With a `figures/` directory next to a copy of `scripts/`, the output is byte-identical to both committed files.
- The 4-panel `epd_rules.tex` (StrictEPD0) is not used by any document.
- Suggested fix: write to `../paper/figures` and `../addendum/figures`.

**C2 (minor): the paper's "9 %" Monte Carlo result depends on the script used.**
- `main_light.tex:332`: "9 % of the updates with the geometric orientation produce negative density or pressure".
- `fallback_positivity.py` gives 1701/20000 = 8.5 %.
- `aligned_flux_diagnostics.py` gives 1797/20000 = 9.0 % for the same experiment (same cloud, same distributions, different RNG stream).
- Both round to "about 9 %", and all other claims hold: 0 inadmissible updates for q = 1 with either orientation, and 0 for q = 3 aligned.
- `fallback_positivity.py` duplicates the helpers of `fallback_positivity_lib.py`. The lib has a stale comment block and an unused `import stencil_diagnostics`.
- Suggestion: cite one script.

**C3 (minor): Table `tab:stencils` mixes two clouds without saying so.**
- The caption says the "perturbed lattice" column is the 300×300 cloud, and almost all its entries do come from that cloud (reproduced exactly: 19.6 (16–22), 1.40 (1.57), 3.79 (4.72), 1.40 (1.55), 3.79 (4.65), 3.5 %, 10.6 %, 4.3 % (18.9 %), 4.0 % (18.5 %), 3.2 %, 44 %, 72 %, 100 %, 0.17 % (4.8 %), 18 % (28 %), 5.3 %, 16.6 %, 73 %).
- The last two rows (5.0 % / 19 %, 0.4 % / 4.7 %) come from `aligned_flux_diagnostics.py` on the **48×48** cloud. The values there are 5.04 %, 18.69 %, 0.40 % and 4.75 %.
- The caption values "without the sweep the pair defects … are 6.2 % and 16.9 %" are not computed by any script provided.
- Derived claims verified:
  - "40–44 %" of the degree-3 weights violate the sign condition.
  - Dissipation factor 3.79/1.40 = 2.7.
  - λΔt/h ≈ 0.32 CFL and 0.11 CFL: from 1/(2 · max ℓ¹ of the no-constant fit) = 1/(2·1.55) and 1/(2·4.65).
- Nit: `stencil_diagnostics.py:149` contains a dead `… if False else …` expression.
- The Tikhonov term `eps0·tr/B` makes the weights exact only to about 1e-10 (q ≤ 2) and 5e-9 (q = 3), which explains the "max 2.5e-11" row sums. This is harmless.

**C4 (major for reproducibility): `figure_measurements/*.py` cannot be run on repository content.**
- The scripts use hard-coded pixel boxes up to row 5828 and column 2959. The committed figures are 2400 px wide (`dmr_density_078.jpg` is 2400×3549, `mach3_density_078.jpg` is 2400×3581).
- The original high-resolution PNG exports they need are not in the repository, so `tab:steppos` ("read from fig:step") and the "x ≈ 2.76 / 2.80" statements on the DMR cannot be reproduced from the archive.
- Other problems:
  - No docstrings or usage notes; `clainpos2.py` needs a comma-separated name list as `argv[2]`.
  - `dmrpos.py:23` has a comment ("midpoint … 60th pct") that does not match the code (threshold `right+40` in colormap-index units).
  - `dmrpos.py` and `steppos.py` print debug lines.
  - `steppos.py:35` raises IndexError if the front never departs.
- Suggestion: add the PNG exports (or their exact sizes and the export command) and a short README.

### fv_reference/

The solver is verified:
- The HLLC and HLL fluxes are consistent (F(U,U) = F(U) on 400 random states).
- On Sod (`test_fv.py`) the x- and y-sweeps give bit-identical results with zero transverse variation. The density L¹ error against the exact solution is 4.76e-3, 2.50e-3 and 1.39e-3 for n = 100, 200, 400 (orders 0.93 and 0.85, as expected for MUSCL-MC on Sod).
- The Riemann problem stays symmetric to 7e-13 at 400².
- The parallel loops (`prange`) write only to their own row/column, so there is no data race.
- A failing fallback raises `RuntimeError` instead of failing silently.

Values re-run against `reference_solutions.md`:

| Quantity | Re-run | `reference_solutions.md` |
|---|---|---|
| RH shock speeds and positions (`rh.py`) | −0.66338/−0.66329/−0.66330 → 0.3010; −0.42208/−0.42233/−0.42180 → 0.3734 | same |
| Three-shock theory (`tst.py`, `tst2.py`) | χ = 7.73°, T = (2.673, 0.340); χ = 10°: 93.12°, ρ = 11.54 | same |
| Sod exact (own solver) | p* 0.30313, u* 0.92745, ρ*L 0.42632, ρ*R 0.26557, head −0.2366, tail −0.0141, contact 0.1855, shock 0.3504 | same |
| DMR 1/120: triple point, χ | (2.7402, 0.4575), 10.08° | (2.740, 0.458), 10.1° |
| DMR 1/120: stem at y = 0.3 / 0.2 / 0.1 / wall | 2.7485 / 2.7575 / 2.7692 / 2.7885 | 2.7485 / 2.7575 / 2.769 / 2.789 |
| DMR 1/120: kink, top row | (2.2104, 0.3955), 3.0543 | (2.210, 0.396), 3.0543 |
| Step 1/40, no fix / WC fix | 0.311, 0.621, 1.207 / 0.307, 0.627, 1.385 | same |
| Step 1/80, no fix / WC fix | 0.312, 0.602, 1.237, triple y 0.73 / 0.312, 0.603, 1.364 | same |
| RP3 400²: curved shock on diagonal, max density | 0.2927; 1.7766 at 0.4288 | 0.293; 1.78 at 0.429 |
| RP3 400²: plane shocks | 0.3006, 0.3728 | (800²: 0.3009, 0.3733) |

Also re-run:

| Quantity | Re-run | `reference_solutions.md` |
|---|---|---|
| DMR 1/240: triple point, χ | (2.7373, 0.4525), 9.98° | (2.737, 0.453), 10.0° |
| DMR 1/240: stem at y = 0.3 / 0.1 / wall, kink | 2.7490 / 2.7754 / 2.8017, (2.2075, 0.3915) | 2.7490 / 2.775 / 2.802, (2.208, 0.392) |
| DMR 1/240 in similarity coordinates (foot, T, kink) | 13.175, (12.853, 2.263), (10.204, 1.958) | identical |
| Step 1/160, no fix | 0.309, 0.593, 1.282, triple y 0.77 | 0.309, 0.593, 1.282, 0.77 |

Not re-run: DMR 1/480, the RP3 800² run, step 1/160 with the fix, and the h = 1/480, t = 0.1 self-similarity run (too slow for this session).

**F1 (minor): the README gives the wrong usage for `fv.py`.**
- README: `python fv.py problem h [limiter] [flux]`. The second argument is actually the integer n = 1/h (`fv.py:288`).
- The codes for limiter (0 = minmod, 1 = MC) and flux (0 = HLLC, 1 = HLL) are not documented anywhere.
- The environment variable `TEND` (used for the self-similarity run) is not documented either.

**F2 (minor): `tst2.py:21` depends on a file that nothing documents.**
- It needs `dmr_240_l1_f0_front.txt` in the current directory, which is produced only by `python fv.py dmr 240` followed by `python analyze.py dmr dmr_240_l1_f0.npz`.
- Without that file it crashes after printing the theory part.

**F3 (minor): two Riemann-problem triple points in `reference_solutions.md` are not what `analyze.py rp3` prints.**
- At 400², the script's 2h criterion gives the lower-left triple point at x = 0.2338. The table says 0.229, which corresponds to a 0.5h threshold.
- For the upper triple point the script gives y = 0.456, against (0.312, 0.473) in the table. That point is where the UR front reaches x ≈ 0.312, which is not a rule in the script.
- These values are not quoted in the paper.
- Suggestion: state the criterion used, or align the script with it.

**F4 (nit): the claim "only the step runs need [the a posteriori fallback]" holds only at the finest step resolution.**
- The fallback is triggered only at h = 1/160 (1 fix).
- The step runs at 1/40 and 1/80, with and without the fix, report `fixes 0`, as do all DMR and Riemann runs.
- Suggestion: say so explicitly.

**F5 (nit): dead code.**
- `RP3.state` has a dead line (`fv.py:220`). The exact plane-shock pattern is used only at t = 0; the boundaries are transmissive, as documented, unlike the meshfree runs, which use exact ghost states.
- `stage(…, last)` is unused.
- The `np.roll` dilation wraps around the domain. This is harmless because the ghost layers are reset.

### stability/scripts/

These results come from the delegated reviewer. I independently re-ran S1.

The data and tables reproduce:
- All RNGs are seeded.
- `make_tables.py` and `ho_make_tables.py` rebuild all 13 `tables/*.tex` byte-for-byte from the committed data.
- Re-generated `.jsonl` and `.md` data match the committed files exactly or to round-off (about 1e-13 relative). The `ho_sos2d` Gram matrix differs by 1.5e-9 between runs, which is solver accuracy.
- Not re-run: `ho_lyapunov` (superseded), the full 180-SDP `ho_defect_cert` sweep (15 cases re-run, all matching), 2-D `ho_defect_random` with A = 0.15, and runs with n ≥ 25600.
- The main reproducibility gap is that no script records the command-line arguments that produced its data file (except three `.txt` files), so the argument sets had to be inferred from the data.

**S1 (major): `ho_common.py:79` (`bloch_symbols`) uses the wrong h for 1-D merge and insert defect cells.**
- It sets `h = 1/(copies·round(N0^(1/D)))`. In 1-D a merge cell has N0 = m − 1 points and an insert cell m + 1, so h is not the lattice spacing 1/(3m).
- As a result the support radius κh is 2.86, 2.67, … spacings (merge) or 2.22, 2.35, … spacings (insert) instead of 2.5, and αh is scaled wrongly. Shift cells and all 2-D cells are not affected.
- With the correct h, K = 2:
  - merge, m = 8, 16, 32, 64: αh = 1.56e-6, 7.5e-8, 1.8e-8, 4.5e-9, against 2.8e-6, 1.1e-7, 2.1e-8, 4.9e-9 quoted in obs:defectbloch(i) and `tab:defectbloch`. The stated decay rate ≈ m^−2.5 changes.
  - insert: 2.6e-6, 8.6e-7, 2.3e-7, 5.7e-8, against 3.3e-8 … 5.8e-10 in `ho_defect_bloch_1d_insert_shift.jsonl`, roughly 80 to 100 times too small.
- The signs (K = 2 unstable, K = 3 at round-off) and the Kreiss constants are essentially unchanged (K = 3, m = 32: merge 1.301 → 1.301, insert 1.093 → 1.099), so the qualitative conclusions survive. The quoted numbers and the rate do not.
- I confirmed this with `test_defect_bloch_h.py`, which prints, for example, merge m = 8, K = 2: script αh = 2.757e-6 against 1.556e-6 with the correct h.

**S2 (minor): `ho_make_tables.py:56` hides a blow-up in `tab:random`.**
- Row (1-D, jitter 0.4, K = 4, geometric): one cloud blows up (αh = 0.95, so no Kreiss value is stored), but the cell shows "2.636–5.177".
- `rng_sci` prints only the maximum αh.

**S3 (minor): SDP solver status is never checked.**
- `ho_defect_cert.py:98` and `ho_defect_cert2d.py:88` store `prob.status` but never check it. 13 of the 180 certificate records are `optimal_inaccurate`, and `Wz.value = None` would crash.
- `bound_omega_h` divides by the requested `cW` rather than the measured λmin(W). This is harmless here (λmin ≥ 0.30).

**S4 (minor): a broad exception handler hides solver errors.** `ho_lyapunov.py:36` has `except Exception` turning solver errors into a status string. The script is superseded, but `tab:measured` still cites its "no diagonal Lyapunov weight for K = 3".

**S5 (minor): some verdicts are floating-point or sampled checks, not proofs.**
- `ho_lyapunov_exact.py` decides "feasible" by |ω_π h| ≤ 1e-12.
- (D4) and the lattice stability claims (`ho_frozen.py`, `lattice_symbols.py`) are checked on sampled θ grids only.
- The RK2 CFL column in `data/lattice_symbols_*.md` (for example 0.090 for K = 4) is a grid artefact; the value is 0, as the text says, and the column is not printed in the table.
- The 2-D unstable αh depends on the grid (8.3e-5 on 101² against the quoted 7.7e-5).

**S6 (minor): text and data disagree in several places.**
- obs:deformed(ii) and tab:measured say "K_V − 1 < 1e-4", but the 2-D data reach 4.8e-4 (K = 2, n = 12). The ω_V bound 4.5e-4 is quoted as "4e-4".
- obs:cert(i) puts K = 3 at ρ = 16 "between 1e-10 and 5e-9", but the minimum is 7.9e-11.
- The spread of ρ_h is "1.2–1.4" in tab:measured and "1.2–1.3" in obs:rho; the data give 1.21–1.34.
- obs:spectra(i): "e^{αt} < 1.002 at N = 3163", but no data file has N = 3163.

**S7 (nit): `ho_defect_cert2d.py:31` does not do what it seems to.**
- The line meant to project G onto the PSD cone is a no-op (λmin(G) = −5.6e-12).
- `tables/ho_defect_cert2d.tex` is empty and never `\input`. This is consistent with "no 2-D certificates".

**S8 (nit): `exact_cert.py` and its results file.**
- `exact_cert.py` closes only the zone inequality exactly; the far-square factor stays in floating point, as the text says.
- `data/exact_cert_results.txt` ends with a leftover line, "… was still running when the report was written".

**S9 (nits).**
- `certify_K2_1d.py:14` defaults to `NMAX = 12` and so prints a failure ("P_10,1 takes negative values"), yet exits 0. The paper uses NMAX = 9.
- Docstring sign error in `ho_defect_cert.py:11` (needs Σ_far B_j ≥ 0).
- The `ho_local_symbol.py` docstring claims the sign of D̄ decides stability, which its own data contradict.
- `spectra_1d.jsonl` mixes records with and without `orient`.

Numbers in `stability_combined.tex` that were checked against data and found to match are listed below; the mismatches are those in S1 and S6.
- obs:random(i, ii), obs:bloch, obs:local, obs:pi, obs:lyapunov, obs:spectra(ii), obs:drift (including the fit and the factor 3.4), obs:moment, obs:rho, obs:cert residuals, obs:super, obs:defectrandom, obs:deformed(iii, iv), obs:sos2d.
- The 1-D jitter-0.2 rows of tab:markov.
- The E₁₂ factorisation and the constant 9 of the obstruction bound.

### results/

**R1 (minor, reproducibility): the run configurations cannot be executed from the archive.**
- The `*_source_N.jl` files `include` base files that are not shipped (`methods_review.jl`, `clainshock.jl`, `DMR.jl`, …), and HyperCloud is not public. So the figures and tables of Sections 5–6 cannot be reproduced from the archive.
- The parameters in the PDEStudio `.csv` exports agree with the paper captions: resolutions 800², 1440×450, 900×300, 330/200 (Sod), N sweeps; jitter 0.2 (0.4 for the conservation-defect study); κ = 2.5 / 5.5; CFL 0.8 (2-D, Float32) and 0.2 (1-D, Float64); final times; method lists.
- The comment in `euler_sod_components_source_1.jl` describes 12 methods while the active list exports the 5 of the figure. This is consistent with the README ("per figure").
- `results/reports/2026-10-29-sod1d.md` and `tab:sod` agree in every digit, and the derived ratios in the text (5.0×, 5.8×) are correct. I did not cross-check the other report tables against the paper.

## Declarations proposed for AIDECL.toml

I did not change AIDECL.toml; another thread consolidates the declarations.

| Path | AI-Generation | AI-Review | AI-Reviewed-by |
|---|---|---|---|
| `scripts/*.py` | G3 | A2 | Claude Opus 5.5 (Anthropic), new session (reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-code-pass2.md) |
| `scripts/figure_measurements/**` | G3 | A1 | (not runnable from the repo, C4) |
| `fv_reference/**` | G3 | A2 | as above |
| `stability/scripts/**`, `stability/data/**`, `stability/tables/**` | G3 | A2 | as above (S1 must be fixed; files changed by the fix fall back to A1) |
| `results/configs/**`, `results/reports/**` | G3 | A1 | (not executable without HyperCloud) |

Human-Review stays with Pascal (TODO).
