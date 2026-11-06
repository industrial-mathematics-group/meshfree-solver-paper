# Supplementary material: meshfree MUSCL schemes with a posteriori order detection
**Dynamic:** 
[![AI generation](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/industrial-mathematics-group/meshfree-solver-paper/badges/ai-generation.json)](https://github.com/industrial-mathematics-group/.github/blob/main/.github/CONTRIBUTING.md#g-generation)
[![Human review](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/industrial-mathematics-group/meshfree-solver-paper/badges/ai-human-review.json)](https://github.com/industrial-mathematics-group/.github/blob/main/.github/CONTRIBUTING.md#h-human-review)
[![AI review](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/industrial-mathematics-group/meshfree-solver-paper/badges/ai-review.json)](https://github.com/industrial-mathematics-group/.github/blob/main/.github/CONTRIBUTING.md#a-ai-review)

**Static:**
![AI generation](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/industrial-mathematics-group/meshfree-solver-paper/badges/aidecl-generation.json)
![Human review](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/industrial-mathematics-group/meshfree-solver-paper/badges/aidecl-human-review.json)
![AI review](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/industrial-mathematics-group/meshfree-solver-paper/badges/aidecl-ai-review.json)

Contents of this archive, by folder:

| Folder | Contents |
|---|---|
| `paper/` | `main_light.tex` / `.pdf`, `refs.bib`, `main_light.bbl` and the figures it includes (`figures/`). Build: `latexmk -pdf main_light.tex`. |
| `addendum/` | Mathematical addendum with the statements and proofs behind the method: `math_addendum.tex` / `.pdf`, bibliography `refs.bib` + `math_addendum_refs.bib`, TikZ figure in `figures/`. Build: `latexmk -pdf math_addendum.tex`. |
| `stability/`  | Stability note `stability_combined.tex` / `.pdf` (bibliography `stability_combined_refs.bib`, tables read from `tables/`). `scripts/` are the NumPy/SciPy/SymPy computations behind the tables and certificates, `data/` their outputs (`.jsonl`, `.md`, `.npy`). |
| `lean/` | Lean 4 formalization (Lake project): `MeshfreeAddendum` (results of the addendum) and `MeshfreeStability` (Part I of the stability note). See `lean/README.md` and `lean/STABILITY.md`. Build: `lake exe cache get && lake build` (toolchain pinned in `lean-toolchain`, Mathlib pinned in `lake-manifest.json`). `AxiomCheck.lean` in each library prints the axioms used. |
| `fv_reference/`  | Finite-volume reference code for the 2-D shock problems (MUSCL with MC limiter, HLLC, SSP-RK3, Numba). `fv.py` is the solver (`python fv.py problem n [limiter] [flux]` with `n = 1/h` cells per unit length, limiter `0` = minmod / `1` = MC, flux `0` = HLLC / `1` = HLL; the environment variable `TEND` overrides the final time), `analyze.py` / `plot.py` extract wave positions and plot, `rh.py`, `tst.py`, `tst2.py` give exact plane- and oblique-shock relations used as checks (`tst2.py` also needs `dmr_240_l1_f0_front.txt` in the working directory, written by `python fv.py dmr 240` followed by `python analyze.py dmr dmr_240_l1_f0.npz`). `reference_solutions.md` gives the reference wave positions (from shock relations and from FV runs at several resolutions) and the method of the FV computations. |
| `scripts/`  | Independent NumPy scripts cited in the paper: `stencil_diagnostics.py` (MLS stencil diagnostics, Table "Stencil diagnostics"), `fallback_positivity*.py` and `aligned_flux_diagnostics.py` (Monte Carlo checks of the first-order fallback, geometric vs aligned flux orientation), `make_epd_figure*.py` (TikZ sketches of the interface rules), `figure_measurements/` (wave positions read from the colour-map figures in `paper/figures/*_078.jpg`; the panels are detected automatically, e.g. `python steppos.py ../../paper/figures/mach3_density_078.jpg`). |
| `results/configs/` | Per figure: the HyperCloud run configurations (`*_source_N.jl`) and the PDEStudio export metadata (`*.csv`: run parameters, axis limits, plot settings). Paths in them are relative to the HyperCloud simulations project. Folders are named after the exported plots (`clainshock` = 2-D Riemann problem, `dmr_*` = double Mach reflection, `mach3step_*` = Mach 3 forward-facing step, `vortex_conv_muscl3` = isentropic vortex). |
| `results/reports/` | Tables of the HyperCloudCore 0.7.8 runs that the paper reports. `RUNS.md` lists the studies, hardware and precision; `2026-10-29-rerun-078-tables.md` (convergence, Euler shock problems, vortex), `2026-10-29-conservation-defect-tables-078.md`, `2026-10-29-sod1d.md`, and `2026-10-29-rerun-078-results.txt` (summary line of every run). |

Python requirements: numpy, scipy, sympy, numba (FV code), matplotlib and pillow (plots and figure measurements); cvxpy for the SDP certificates in `stability/scripts`.
