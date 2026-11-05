# Changes of 5 Nov 2026: fixes from the reviews of commit a6edcc9

Fixes for the findings of the independent reviews of `a6edcc9`: paper pass 1 (PR #5) and pass 2 (PR #3), code pass 1 (PR #6) and pass 2 (PR #4), and Lean (PR #7, plus the Thm 4.1(iv) item of PR #8). Finding IDs refer to those review files. All edits were made by one Claude Opus 5.5 session. Every changed file is back at **A1** until it is reviewed again.

There is no full paper in the repository (only `paper/main_light.tex`), so nothing was deleted. The repository now holds the light paper, the addendum and the stability note.

## Rerun after this change

| What | Command | Expected |
|---|---|---|
| Wave positions, Mach 3 step (`tab:steppos`) | `cd scripts/figure_measurements && python steppos.py ../../paper/figures/mach3_density_078.jpg` | bow 0.302/0.305/0.306/0.305, stem 0.582/0.585/0.585/0.585, reflection 1.313/1.290/1.262/1.238 (EPD1-K3, EPD2-K3, EPD1-K4, EPD2-K4); triple point y ≈ 0.73 |
| DMR stem / incident shock | `python dmrpos.py ../../paper/figures/dmr_density_078.jpg` | K=2 foot 2.788, K≥3 stem 2.74–2.77, incident 3.047–3.049 |
| Riemann plane shocks | `python clainpos2.py ../../paper/figures/riemann2d_density_078.jpg` | 0.370–0.374 and 0.299–0.301 |
| Stencil table (`tab:stencils`) | `cd scripts && python stencil_diagnostics.py` (n = 300) | unchanged values; it now also prints the no-sweep (6.2 % / 16.9 %) and equal-volume (5.7 % / 16.7 % / 72.9 %) pair defects and the sign-mismatch rows (5.02 % / 18.75 %, weight 0.39 % / 4.71 %) |
| Monte Carlo, geometric vs aligned | `python aligned_flux_diagnostics.py`, `python fallback_positivity.py` | both 1797/20000 = 9.0 % for degree 3, geometric (before: 8.5 % from the second script) |
| EPD sketches | `python make_epd_figure_light.py`, `python make_epd_figure_addendum.py` | byte-identical to `paper/figures/epd_rules_light.tex`, `addendum/figures/epd_rules_addendum.tex` |
| Defect Bloch arrays | see the commands in the next section, then `python stability/scripts/ho_make_tables.py` | numbers below |
| K = 2 lattice certificate | `python stability/scripts/certify_K2_1d.py` | passes for n ≤ 9 (default changed from 12 to 9) |
| PDFs | `latexmk -pdf` in `paper/`, `addendum/`, `stability/` | built without undefined references; `.bbl` files unchanged |

The 1-D defect data were regenerated with:
```
S=stability/scripts/ho_defect_bloch.py
python3 $S 1 8,16,32,64 2,3,4 64 stability/data/ho_defect_bloch_1d.jsonl geometric,aligned merge
python3 $S 1 128 2,3 64 stability/data/ho_defect_bloch_1d.jsonl geometric,aligned merge
# insert and shift, per K in 2 3 4 and orient in aligned geometric (m up to 64 for K = 4, else 128):
python3 $S 1 8,16,32,64,128 K 64 stability/data/ho_defect_bloch_1d_insert_shift.jsonl ORIENT TYPE
```
The shift records and the 2-D data are unchanged. Only the merge and insert cells were affected by the bug.

## Changed files

### `paper/main_light.tex` (+ rebuilt `main_light.pdf`)
- **Lean removed**: the AI declaration no longer mentions a Lean formalization or a Lean rebuild. It now also says that the run-report tables were compiled with Claude Opus 5.5 (P12). No other Lean reference existed.
- `:248` (P1/S4): the coupled and frozen modes coincide only if no order is lowered **and** q(k_div) = q(K), in particular for K ≤ 2.
- `:263` (S1): K = 1 uses the aligned orientation only when the aligned flux is selected; the RK2MUSCL1 baseline uses the geometric one. The "5 % / 19 %" sentence now points to the clouds of `tab:stencils`.
- `:285`: the FV form holds by definition; antisymmetry is what makes it conservative.
- `:330`: the scalar maximum-principle bound also needs s ≥ |F'| between U_i and U_j.
- `:332` (minor, P8): "40–44 % … even on lattices" → 40 % on lattices, 44 % on perturbed clouds; "9 %" → "about 9 %", on a perturbed 48×48 cloud.
- `:394` (P7/S2): the time-step weights have degree q(k_div) in frozen mode and q(K) in coupled mode (was "full-order degree").
- `:410`, `:512` (P11): "5 to 30 times smaller" → "at the finest resolution".
- `:418`: "same boundary conditions" → "same types of boundary conditions".
- `:559` (P10): "decays by a factor of about e³" → "varies strongly".
- `:563`: equal-volume mixed pair defect 72.8 % → **72.9 %** (300×300 cloud, now printed by the script).
- `:686` (P4–P6, S6):
  - "All 60 runs" → "All 57 runs, and the three Riemann runs with transmissive boundaries";
  - lowest pressure: only 4.8·10⁻³ (K=3, k_div=K, EPD1) is named; the "3.4·10⁻² for K=4" claim is dropped;
  - min p ≥ 0.25 → **≥ 0.249**; 38 % → **39 %**; "within 4 %" → "within about 4 %";
  - step counts: compared with 13.5·10³ for RK2MUSCL2 **and** 13.1·10³ for RK2MUSCL1.
- `:756` (P3): DMR second-order stem foot x ≈ 2.80 → **2.79**.
- `tab:steppos` and `:784` (P2/E1), measured with the fixed `steppos.py`:

  | run | bow shock | Mach stem | reflection |
  |---|---|---|---|
  | RK3MUSCL3(EPD1,MLS3) | 0.29 → **0.30** | 0.57 → **0.58** | 1.31 |
  | RK3MUSCL3(EPD2,MLS3) | 0.29 → **0.30** | 0.57 → **0.59** | 1.28 → **1.29** |
  | RK4SSPMUSCL4(EPD1,MLS4) | 0.29 → **0.31** | 0.57 → **0.59** | 1.25 → **1.26** |
  | RK4SSPMUSCL4(EPD2,MLS4) | 0.29 → **0.30** | 0.57 → **0.59** | 1.23 → **1.24** |

  - The text now reads "agree with those of the finest reference computation to within about 0.01" (was "about 0.02 upstream").
  - Triple point y ≈ 0.75 → **0.73**.
  - The reflection range is now 1.31 → 1.24, and the bow shock and stem are the same in all runs "to within 0.005".

### `addendum/math_addendum.tex` (+ rebuilt `math_addendum.pdf`)
- Abstract (A1/E3): "four interface rules" → **three**. The RK2/RK3 stage-value claim is now justified: their stages contain only Uⁿ and the last substep (A5).
- `rem:lean` (A3/A4/S8): rewritten to list the restrictions.
  - Lemma 3.7(iii): only 17/5 ≠ 0 is in the library.
  - Props 5.2/5.3/5.7: checked with s > 0 for all j, d and λ > 0; the aligned version takes the zero row sums as a hypothesis.
  - Thm 6.3/Cor 6.4: hSO, (H3), exact locality, and `hone`, which is stronger than (H4).
- `rem:stagevalues` (A5): new justification, "row k contains only Uⁿ and W_{k−1}, then Prop 5.7 + convexity". The 0.5172 coefficient is explained as coming from the unrounded tableau (0.5173 from the rounded table).
- `rem:mood(iv)` (A2): "satisfies (eq:dmp)" → "is not flagged by (eq:dmp), i.e. lies in [Y^min, Y^max]".
- `rem:mood(iii)` (A8): "k_div = K ≥ 3" → "K ∈ {3, 4}".
- Prop 5.7 and Thm 6.3 (H4) (S7): now state s_{ij,d} > 0 wherever c ≠ 0.
- Cor 6.4 (A7): states its CFL condition directly instead of invoking (H4).
- Conservation remark (A6): wording of the (iii) step and of the FV form.
- Lemma 4.1: "strictly opposite signs" is sufficient, not necessary.
- Lemma 6.1: added a remark that it holds with a different operator per stage.
- `:171`: B defined. `:650`: "both drafts" → "the draft". Date: "revised 5 November 2026".
- Not done: the notation overloads (A9/S9). This would be a larger rename; it needs Pascal's go-ahead.

### `stability/stability_combined.tex` (+ rebuilt `.pdf`), tables and data
- **Bug S1 (code pass 2):** `ho_common.bloch_symbols` used h = 1/(3·round(N0)) for 1-D merge/insert cells. It now takes the lattice m from `ho_defect_bloch.py`.
  - New K=2 αh, merge, m = 8…128: 2.8e-6, 1.1e-7, 2.1e-8, 4.9e-9, 1.2e-9 → **1.6e-6, 7.5e-8, 1.8e-8, 4.5e-9, 1.1e-9**.
  - New K=2 αh, insert: 3.3e-8 … 1.5e-10 → **2.6e-6, 8.6e-7, 2.2e-7, 5.7e-8, 1.4e-8**.
  - The decay rate in `obs:defectbloch(i)` changes from ≈ m^−2.5 to **≈ m^−2**, so the residual bound becomes ≳ ϱ^−2 and α ≈ c·h/ℓ².
  - Insert K=3 Kreiss constant 1.09 → **1.10**. Kreiss constants in `tab:defectbloch` change in the third digit (e.g. K=4 merge, geometric: 1.636 → 1.646 at m = 8). Signs and conclusions are unchanged.
- `tables/ho_random.tex` (F1/S2): the Kreiss range of (1-D, jitter 0.4, K=4, geometric) is `2.636--5.177` → **`2.636--∞`**. `ho_make_tables.py` now shows ∞ whenever a cloud blows up.
- Cor 8.8(i) (Lean S8): the threshold is now ϱ_h ≥ c⁻¹ log(C₀/(2 min(c_W,1) g₋ h)), matching the proof.
- AI declaration (Lean S9): "a partial Lean 4 formalization of Part I … several analytic steps enter as hypotheses".
- S6 (code pass 2):
  - K_V − 1 < 1e-4 → < 1e-4 (1-D), < 5e-4 (2-D);
  - ω_V up to 4e-4 → 4.5e-4;
  - cert residual at ϱ = 16 between 1e-10 → **8e-11** and 5e-9;
  - ρ_h spread → 1.21–1.34 in both places;
  - e^{αt} < 1.002 at N = 3163 is marked as extrapolated.

### Scripts and code
- `scripts/figure_measurements/{steppos,dmrpos,clainpos2}.py` + new `frames.py` (P3/E2/C4/S2): the panels are now detected from the frame lines and the plot aspect ratio, instead of hard-coded pixel boxes of old exports. The scripts run on the shipped JPGs and have usage docstrings.
- `scripts/make_epd_figure_light.py`, `_addendum.py` (S10/C1/S1): now write to `paper/figures/` and `addendum/figures/`. `make_epd_figure.py` writes its unused 4-panel sketch to the current directory.
- `scripts/stencil_diagnostics.py` (C3/S3, P8): prints the sign-mismatch rows on the 300×300 cloud, plus the no-sweep and equal-volume pair defects. All numbers of `tab:stencils` now come from this one script. The dead `if False` expression was removed.
- `scripts/fallback_positivity.py`, `fallback_positivity_lib.py`, `aligned_flux_diagnostics.py` (P9/C2/S4/S5):
  - `fallback_positivity.py` now reuses the same Monte Carlo function and seeds, so both scripts give 9.0 %;
  - the duplicated helpers, the unused import and the stale docstrings are gone.
- `fv_reference/fv.py`, `README.md` (F1/FV1): the usage is now `problem n [limiter] [flux]` with n = 1/h, the limiter and flux codes are documented, and so is `TEND`. `tst2.py` and the README document the `dmr_240_l1_f0_front.txt` input (F2).
- `fv_reference/reference_solutions.md` (F4/FV4): only the step run at h = 1/160 triggers the fallback (one fix).
- `stability/scripts/ho_defect_cert.py`: docstring sign (Σ_far B_j ≥ 0).
- `stability/scripts/certify_K2_1d.py`: default NMAX 12 → 9, as in the note.
- `results/reports/2026-10-29-sod1d.md`: "L1 order 0.9 … 1.06" → 0.87 … 1.06.

### Lean documentation (no Lean statement changed)
- `lean/STABILITY.md`: relabelled per the Lean review (S1–S7) and PR #8.
  - Thms 6.1, 7.3, 8.7, Lemma 8.1, Lemma 8.4, Thm 4.1(iv) and Prop 9.2 → Partial;
  - Cor 7.4 → Not done;
  - Prop 4.3 → Checked, hyp.;
  - Cor 6.4 now lists `hnorm` and `happrox`; Prop 4.5(i) notes s > 0.
  - Count 6/10/13/1 → **2/7/19/2**.
- `lean/MeshfreeAddendum/AxiomCheck.lean`: comment only. The reference to the missing `ReviewCompositions.lean` was dropped (A10/A5).

## Open, needs Pascal or data that is not in the repository
1. **K = 5 neighbour explanation (paper `:620`, S3 of paper pass 1).** At θ = 0.4, κ = 5.5 every 1-D stencil has at least 9 = 1.5·6 neighbours, so with the "at least 1.5×" rule of `:246` no stencil falls back. The explanation holds only if HyperCloudCore's safeguard is strict (> 1.5×). Which one does the code use? The text is unchanged until that is known.
2. **`tab:vortex` L² errors (S5/R2)** and the intermediate errors of `tab:conv` and the Sod table are not in `results/reports`. "π₀ = 10⁻² at N = 100" (`:559`) has no run in the reports either. These need the HyperCloud outputs.
3. **AI declaration in the paper (P12):** "the authors … verified all content" and the review claims are Pascal's statement to make.
4. `results/reports/RUNS.md` says PDEStudioCore 0.4.2 while the CSVs say PDEStudio 0.4.5. These may be two packages; please confirm. Stale comments in `results/configs/*` (Pascal's files, G0) were not touched.
5. Addendum notation overloads (A9/S9) and moving the Lemma 3.7(iii) proof from the Lean review into `MLS.lean` (needs a Lean build).
