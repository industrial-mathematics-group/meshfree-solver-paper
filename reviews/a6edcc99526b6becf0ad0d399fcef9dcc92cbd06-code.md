# Independent code review (A2) of commit a6edcc9: scripts, FV reference, stability scripts, results

- Commit reviewed: `a6edcc99526b6becf0ad0d399fcef9dcc92cbd06` (main, 5 Nov 2026)
- Reviewer: Claude Opus 5.5 (Anthropic), new session with no access to the chats or notes that generated the files.
  It saw only the repository. The stability scripts were reviewed by a second, separate Opus 5.5 subagent with the
  same restriction; its findings are merged below (section 4) and were spot-checked by the reviewer (F1 confirmed).
- Scope: everything outside `lean/`, `paper/*.tex`, `addendum/*.tex` and `stability/*.tex` that is code, or that
  code produced: `scripts/`, `fv_reference/`, `stability/scripts/`, `stability/data/`, `stability/tables/`,
  `results/configs/`, `results/reports/`. The prose of the paper, addendum and stability note was only read where
  it quotes numbers that these files produce.
- Environment: Python 3, numpy, scipy 1.18, sympy 1.14, numba 0.68, cvxpy 1.9 (Clarabel/SCS), matplotlib, pillow;
  4 CPU cores. HyperCloud / HyperCloudCore (Julia) is **not** part of this repository and was not run.
- The repository has no test suite. The checks below are the scripts' own runs plus the extra tests in
  `reviews/a6edcc99526b6becf0ad0d399fcef9dcc92cbd06-code/` (run them from the repository root; the ones in
  `stability/` import `stability/scripts` by a path relative to their own location).

## Summary

The numerics are sound. Every number of the paper that one of these scripts produces and that could be
regenerated here was regenerated and agrees: the stencil-diagnostics table, the Monte Carlo positivity
percentages, the FV reference values at the resolutions that were run, the Sod exact solution, the
shock-relation values, all 13 stability tables (byte-identical) and nearly all stability data (bit-identical or
round-off). The Euler-problem tables of `results/reports` agree with the per-run log and with Table
`tab:euler2d` of the paper.

There is one defect that changes a number shown in a paper document (F1, stability table `ho_random.tex`), one
broken output path (S1) and a set of reproducibility gaps, mainly that the inputs of
`scripts/figure_measurements/` and some FV reference values cannot be regenerated from the repository.

| Severity | Count | Items |
|---|---|---|
| affects a published number | 1 | F1 |
| bug, no effect on published results | 3 | S1, F2, FV3 |
| reproducibility / documentation | 10 | S2–S5, FV1, FV2, FV4, R1–R3, F9 |
| style | several | listed per file |

## 1. `scripts/`

### What was run

| Script | Run | Result vs. paper |
|---|---|---|
| `stencil_diagnostics.py` (48² lattice, 48² and 300² perturbed) | full | every entry of Table `tab:stencils` reproduced, see below |
| `fallback_positivity.py` | full (2×20000 trials) | degree 1: 0/20000 inadmissible; degree 3: 1701/20000 = 8.5% (paper: "9%") |
| `aligned_flux_diagnostics.py` | full | degree 3: geometric 1797/20000 = 9.0%, aligned 0; degree 1: 0 and 0; sign mismatch 5.04%/0.40% (q=1), 18.69%/4.75% (q=3) — paper: 5%/0.4%, 19%/4.7% |
| `make_epd_figure_light.py`, `make_epd_figure_addendum.py`, `make_epd_figure.py` | in a scratch copy (see S1) | output byte-identical to `paper/figures/epd_rules_light.tex` and `addendum/figures/epd_rules_addendum.tex` |
| `figure_measurements/*.py` | not runnable (S2) | — |

Stencil table, perturbed 300×300 column, script output vs. paper: neighbours 19.62 (16–22) / 19.6 (16–22);
ℓ¹ 1.399 (1.567), 3.792 (4.721) / 1.40 (1.57), 3.79 (4.72); without constant term 1.400 (1.553), 3.787 (4.654) /
1.40 (1.55), 3.79 (4.65); rel. difference 3.5%, 10.6% / same; row sums 4.3% (18.9%), 4.0% (18.5%) / same; sign
violations 3.2%, 44.2%, particles 72%, 100%, share 0.17% (4.8%), 17.94% (28.1%) / same; pair defect 5.3%, 16.6%,
mixed 72.9% / 5.3%, 16.6%, 73%. Lattice column: 1.359, 3.593, 40.0%, 17.53%, mixed 73.1% / 1.36, 3.59, 40%, 17.5%, 73%.

Extra checks (`stencil_extra.py`):
- Polynomial exactness of the MLS derivative weights: monomials up to degree q are differentiated with error
  1.1e-10 (q=1) and 7.9e-9 (q=3) — the size of the Tikhonov term `eps0 = 1e-10`, as expected.
- Pair defects quoted in the paper but **not printed by any script**: equal volumes 5.7%, 16.7%, 72.9% (paper
  Sec. 6: 5.7%, 16.7%, 72.8%); Shepard volumes without the smoothing sweep 6.2%, 16.9% (table caption: 6.2%,
  16.9%). Both confirmed. The mixed value 72.8% in the text matches the 48² cloud, the 300² cloud gives 72.9%.

The positivity argument in the MC scripts was checked by hand: with zero row sums,
`U_i + Δt·(−2Σ c(F* − F_i))` with `Δt = 1/Σ s|c|` is exactly the convex combination (eq. `convex` of the paper)
when the orientation is aligned, so "0 inadmissible" for the aligned flux is the expected outcome, and the
geometric failures come from the entries with `sgn(c) ≠ sgn(x)`.

### Findings

- **S1 (bug, no effect on the paper): output paths do not exist in this layout.** All three
  `make_epd_figure*.py` write to `scripts/../figures/…` (`make_epd_figure.py:82`, `_light.py:15`,
  `_addendum.py:15`), i.e. a top-level `figures/` that is not in the repository. Run as documented they fail with
  `FileNotFoundError`. The targets should be `paper/figures/epd_rules_light.tex` and
  `addendum/figures/epd_rules_addendum.tex`. `make_epd_figure.py` (4 panels incl. StrictEPD0) produces
  `epd_rules.tex`, which no document uses.
- **S2 (reproducibility): `figure_measurements/` cannot be run on anything in the repository.** The three scripts
  take a PNG/JPG path and hard-code pixel boxes (`R`, `C`, `c0, c1`) of the original full-resolution PDEStudio
  exports (e.g. rows up to 5828 px in `dmrpos.py`/`steppos.py`, columns up to 3428 px in `clainpos2.py`). The
  committed `paper/figures/*_078.jpg` are 2400 px wide with other layouts, so the measured positions in the
  paper (Table `tab:steppos` and the DMR/Riemann positions) cannot be regenerated. There is no docstring or usage
  line, and the scripts print the frame detection (`rows, cols`) but then ignore it. Either add the raw exports
  (or their file names and sizes) or state in the README that the inputs are not included.
- **S3 (reproducibility): the last two rows of `tab:stencils` come from a different cloud than the caption says.**
  The sign-mismatch rows ("pairs and directions with c_ij c_ji > 0", 5.0%/19%, 0.4%/4.7%) are computed by
  `aligned_flux_diagnostics.py` on the 48×48 perturbed cloud, while the caption describes the 300×300 cloud. The
  values are close, but the caption or the script should be aligned. The Monte Carlo tests also use the 48² cloud.
- **S4 (reproducibility): two scripts give two different "geometric degree-3" rates.** `fallback_positivity.py`
  (one RNG stream across both degrees) gives 8.5%, `aligned_flux_diagnostics.py` (fresh seed per call) 9.0%. Both
  round to the paper's "9%" only loosely; cite which script the number comes from.
- **S5 (style): duplication and dead code.** `fallback_positivity.py` duplicates the Euler helpers of
  `fallback_positivity_lib.py` instead of importing them; `fallback_positivity_lib.py` imports
  `stencil_diagnostics` without using it and its first comment describes the Monte Carlo script, not the helpers;
  `stencil_diagnostics.py:149` has `... if False else ...` dead code.

## 2. `fv_reference/`

### What was run

| Run | Result | `reference_solutions.md` |
|---|---|---|
| `rh.py` | speeds −0.66338/−0.66329/−0.66330, −0.42208/−0.42233/−0.42180; positions 0.3010, 0.3734 | identical |
| `tst.py` | χ = 7.735°, triple point (2.673, 0.340), p ratio 116.5, ρ ratio 5.714 → ρ = 8.000 | identical |
| independent exact Sod solver (`sod_exact.py`) | p* 0.30313, u* 0.92745, ρ*L 0.42632, ρ*R 0.26557, head −0.2366, tail −0.0141, contact 0.1855, shock 0.3504 | identical |
| `fv.py step 40`, `analyze.py step` | bow 0.311, stem 0.621, step reflection 1.207 | identical |
| `fv.py stepfix 40` | 0.307, 0.627, 1.385 | identical |
| `fv.py step 80` / `stepfix 80` | 0.312 / 0.312, 0.602 / 0.603, 1.237 / 1.364, triple point y 0.73 | identical |
| `fv.py dmr 120`, `analyze.py dmr`, `dmr2` | TP (2.7402, 0.4575), χ 10.08°, stem 2.7485 / 2.7575 / 2.7692 at y = 0.3/0.2/0.1, foot 2.7885, kink (2.2104, 0.3955), top row 3.0543 | identical to the h = 1/120 column |
| `fv.py rp3 200` | plane shocks 0.3004 / 0.3731, symmetric to 3e-14 | consistent with the 400²/800² values (not run) |

Not run for time: DMR h = 1/240 and 1/480, step h = 1/160, Riemann 400² and 800², and therefore `tst2.py`.

Code checks: HLLC (Toro's star states, Einfeldt–Roe speeds), MC limiter, SSP-RK3 stage weights and boundary
times, wall mirroring for both face orientations, the ghost-cell mirrors of the step's top and bottom walls, and
the DMR/step/Riemann data all checked line by line and correct. The first-order fallback raises
`RuntimeError` after four enlargements rather than continuing silently.

### Findings

- **FV1 (documentation): the usage line is wrong.** `fv.py` docstring and the README say
  `python fv.py problem h`, but the second argument is `n` with `h = 1/n` (`fv.py:292`). `python fv.py dmr 0.01`
  crashes. Also the time can be overridden with an undocumented `TEND` environment variable (used for the
  self-similarity run).
- **FV2 (reproducibility): several reference values are not produced by any script.** The wall-jet vortex centre,
  the jet cap on the diagonal, "UR shock near the interaction", the Kuhl et al. ratios and the slip-line
  stagnation point are not computed by `analyze.py` (the diagonal is only written to `*_diag.txt`), so they were
  read by hand. `tst2.py` needs `dmr_240_l1_f0_front.txt` in the working directory (an output of a 1/240 run,
  not committed) and `exec`s the first half of `tst.py`.
- **FV3 (minor bug, no effect): `analyze.dmr` prints a spurious triple point.** The ">1h" criterion jumps to
  y = 0.904 at h = 1/120 (the top boundary region), and the path angle it prints (9.2°) disagrees with `dmr2`
  (10.08°). The reference file correctly uses `dmr2`. `RP3.state` contains dead code (`top = ... if False else
  None`, unused `xa`, `xb`), and `stage(..., last=True)` is unused.
- **FV4 (claim not confirmed at the resolutions run): "Only the step runs need [the fallback]".** At h = 1/40
  and 1/80 the step runs also need no fixes (`fixes 0`); DMR 1/120 and Riemann 200² also 0. The statement may
  hold at 1/160 but was not verified.

## 3. `results/`

HyperCloud is not in the repository, so no run could be repeated. Checked instead:

- `results/reports/2026-10-29-rerun-078-tables.md`, Euler section: all 60 rows (status, min ρ, min p, mass
  change, steps, runtime) agree with the job lines of `2026-10-29-rerun-078-results.txt` (`crosscheck_tables.py`).
- Paper Table `tab:euler2d` (min p and relative masses) recomputed from those rows (`crosscheck_euler2d.py`,
  using that the "mass change" column is the relative drift m(T)/m(0) − 1): all cells agree, as do the text
  claims (coupled mode −3.5%, +5.4%, +4.7%, +1.4%; EPD2 −2.0 to +0.8%; frozen within 0.25%).
- `2026-10-29-conservation-defect-tables-078.md`: all 151 data rows occur verbatim in the results log.
- Paper Table `tab:conv`: all 60 orders recompute from the tabulated errors and N (`check_orders.py`); the N = 3163
  errors and the κ = 2.5 rows equal the report's "L1 at N_max".
- `2026-10-29-sod1d.md` vs. paper: 5.0× and 5.8× below MUSCL1, 0.87–1.06, mass change 2.5e-5 to 1.2e-4, min ρ —
  all consistent.
- Configs: DMR post-shock state (8, 57.1577, −33, 563.5), Mach 3 inflow (1.4, 4.2, 0, 8.8), grid sizes, CFL 0.8,
  κ = 2.5, perturbation 0.2, Float32 overrides and N sequences agree with `tab:setup`, `RUNS.md` and the reports.
  The vortex exact solution and the conservation-defect post-processing (`*_source_*.jl`) are correct as written.

### Findings

- **R1 (reproducibility): the configs cannot run on their own.** They `include` `../methods_review.jl` and
  `DMR.jl`, which are not in the repository, so the method definitions behind labels such as
  `RK3MUSCL3(EPD1,AR,MLS2)` are not recoverable from the supplement. The README says paths are relative to the
  simulations project; it should also say that `methods_review.jl` (and HyperCloud's built-in examples such as
  `euler_1d_sod`) are needed.
- **R2 (reproducibility): intermediate errors are not in the supplement.** The per-N errors of `tab:conv`,
  `tab:vortex` and the Sod table (N = 100, 317) appear only in the paper; the reports give N_max values and EOCs.
- **R3 (documentation):** `RUNS.md` names PDEStudioCore 0.4.2, the CSV metadata name PDEStudio 0.4.5 (possibly
  different packages; worth one sentence). The DMR config comment "a fixed order 3 … blow[s] up on the 2-D
  problems" is stale: the MLS3 runs in the tables finished. `sod1d.md` says "L1 order 0.9 … 1.06" while its own
  table has 0.87 (paper correctly says 0.87). The results log contains 162 `FAIL … NO DATA` lines from 18 jobs;
  none of them is referenced by a report table (studies outside this paper), but RUNS.md could say so.

## 4. `stability/scripts`, `stability/data`, `stability/tables`

Reviewed by the separate subagent. Re-run: lattice symbols (paper grids), all spectra files, ho_random,
ho_bloch (+ mpcheck), ho_defect_bloch, ho_defect_cert (all 180 records bit-identical), ho_defect_random,
ho_deformed (+ squares), ho_frozen, ho_pi, ho_lyapunov(_exact), ho_local_symbol, ho_nn_identity,
ho_nn_admissible, ho_defect_pi, certify_K2_1d (n ≤ 9 pass, P_{10,1} fails), d5_check, k2_random_search,
first_order_* (corrector_large up to N = 102400), exact_cert (one of six certificates), ho_sos2d (Gram matrices
differ by ≤ 5e-7, min eigenvalue unchanged). Shortened: ho_defect_cert "super" (4 of 25 configurations),
ho_lyapunov SCS (subset). Not run: `ho_defect_cert2d.py` (the note says it runs out of memory; its table is not
`\input`). `make_tables.py` and `ho_make_tables.py` regenerate all 13 `tables/*.tex` byte-identically from the
committed data. Independent tests in `…-code/stability/`: separate 1-D operator assembly (≤ 1e-14), Bloch
symbols vs. the full periodic operator (≤ 2e-14), Lyapunov/Kreiss brute force, Fejér–Riesz squares (2e-14),
brute-force 2-D lattice instability (7.72e-5, 2.10e-3 vs. 7.7e-5, 2.2e-3 in the note).

### Findings

- **F1 (affects a published number): blow-ups dropped from a Kreiss range.** `ho_make_tables.py:56` builds the
  𝒦 range only from clouds that have a Kreiss value. In `tables/ho_random.tex:10` (D = 1, jitter 0.4, K = 4,
  geometric) the cell reads `2.636--5.177`, but the n = 200, seed 0 cloud has α h = 0.949 and no Kreiss
  constant (confirmed in `data/ho_random_1d.jsonl`). The cell should show ∞ (or "2.636–∞"). The α h column and
  the text do report the blow-up. `make_tables.py:75` and `ho_make_tables.py:233` handle this correctly.
- **F2 (data file only): tolerance artefact.** `lattice_symbols.py:67` accepts max|R| ≤ 1 + 1e-12, which yields
  nonzero "CFL_max RK2" for K = 4, 5 (0.061, 0.093, 0.090) in `data/lattice_symbols_*.md`; at those CFLs the
  excess is exactly 1.0e-12 (`t5_rk2_tolerance.py`). The column is not in the table, and the note's statement
  that RK2 is unstable at every time step for K = 4, 5 is correct; the data file should flag these values.
- **F3:** `ho_defect_cert.py:98` and `ho_defect_cert2d.py:88` do not check the cvxpy status; 13 of 180
  certificates are `optimal_inaccurate` (K = 4, ρ ≥ 12). Mitigated: t, w_min, w_max are recomputed a posteriori
  from the returned W, so the reported values are valid. The status could be stored in the data.
- **F4 (style):** `ho_defect_cert2d.py:31` multiplies its correction by `*0`; the B_j ≥ 0 assumption is not
  enforced (G has min eigenvalue −5.6e-12). Disclosed in the note; no 2-D certificates are claimed.
- **F5 (style):** docstring sign in `ho_defect_cert.py:11` ("≤ 0" should be "≥ 0").
- **F6 (no effect):** `d5_check.py:21` discards the division remainder; it is ≤ 3e-15 relative (`t7`), and the
  minima 0.261 / 0.251 / 0.027 / 0.630 are confirmed by direct evaluation.
- **F7 (style):** `first_order_phase.py:4` says "ℓ²(π) sense" for a plain least-squares fit; the note calls the
  first-order operator "sparse" while `linop.first_order_operator` is dense.
- **F8 (consistent with the note):** Kreiss constants are maxima over 26–40 time samples; a finer grid gives up
  to 4% more (2.61 → 2.71, `t8`). The note calls them lower bounds.
- **F9 (reproducibility):** most data files do not record the command line; `ho_frozen` data need odd θ counts
  (201, 61) to avoid θ = 0; `exact_cert_results.txt` ends with a truncated, labelled entry.

## 5. Declarations

Recommended AI-review levels after this review (G as currently declared; Human-Review stays with Pascal). A2 is
given where the reviewer re-ran the code and checked its outputs; files that could only be read stay at A1.

| Path | G | A | Note |
|---|---|---|---|
| `scripts/stencil_diagnostics.py`, `fallback_positivity*.py`, `aligned_flux_diagnostics.py` | G3 | A2 | S3–S5 |
| `scripts/make_epd_figure*.py` | G3 | A2 | S1 (path) |
| `scripts/figure_measurements/**` | G3 | A1 | not runnable without the raw exports (S2) |
| `fv_reference/*.py` | G3 | A2 | FV1–FV4; `tst2.py` only read (needs a 1/240 run) |
| `fv_reference/reference_solutions.md` | G3 | A2 | values checked at the resolutions run; FV2, FV4 |
| `stability/scripts/**` | G3 | A2 | F1–F9; fix F1 before the next table build |
| `stability/data/**` | G3 | A2 | regenerated (bit-identical or round-off) |
| `stability/tables/**` | G3 | A2 | regenerated byte-identically; `ho_random.tex` carries F1 |
| `results/reports/**` | G3 | A2 | internal consistency and agreement with the paper checked; runs not repeatable here |
| `results/configs/**` | G3 | A1 | Julia, not runnable without HyperCloud and `methods_review.jl` (R1); read only |
| `reviews/**` | — | — | to be excluded in `AIDECL.toml` |

`Assisted-by` note: `git log` shows that commit `824d923` (Opus 5.5) changed `fv_reference/analyze.py`,
`fv_reference/reference_solutions.md`, `results/reports/2026-10-29-sod1d.md` and several `stability/scripts`
and `stability/data` files, while `AIDECL.toml` names only Fable 5.1 for `fv_reference/**`, `scripts/**` and
`stability/**`. Those files should list both models. The reviewer is the same model family as one of the
generators, so this review is A2, not A3.
