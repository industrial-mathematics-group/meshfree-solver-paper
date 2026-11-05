# Independent review (pass 2) of the review fixes, PR #9 and PR #11

- **Reviewed commit:** `627fab6ad80f99057b8ddf62f0feb2b412e9e132`, the head of PR #11 (open). It sits on `885c822`, the merge of PR #9 into `main`. The diff reviewed is `a6edcc9..627fab6` without `reviews/`.
- **Reviewer:** Claude Opus 5.5 (Anthropic), a new session. It had no access to the session that made the fixes, nor to the other review threads or any other review of these fixes. The reviews of `a6edcc9` (PRs #3–#8) were read only to know what had to be fixed.
- **Date:** 5 November 2026.
- **Extra code:** `reviews/627fab6ad80f99057b8ddf62f0feb2b412e9e132-fixes-pass2/` holds three small check scripts.

## Summary

The fixes are correct. Every rerun command in `CHANGES.md` reproduces its stated output exactly, and the three PDFs build cleanly. Their text matches the committed PDFs.

I found two new should-fix problems. Both are text that was not updated to match the fix.

- **N1, stability note.** After the `bloch_symbols` fix, the periodic array of insert defects with K = 4 and the aligned orientation is weakly unstable. The note still says α = 0 there.
- **N2, paper `:620`.** The K = 5 explanation still says the fit "requires 9 neighbours" and that "some stencils have fewer". Under the strict rule the fit needs more than 9, and no stencil has fewer than 9: about 11 % have exactly 9. `CHANGES.md` says the sentence "stands as written". It does not.

The rest is minor.

## What was run

| Check | Result |
|---|---|
| `steppos.py`, `dmrpos.py`, `clainpos2.py` on the shipped `*_078.jpg` | Identical to `CHANGES.md`. Bow shock 0.3017/0.3045/0.3059/0.3045, stem 0.5823/0.5851/0.5851/0.5851, reflection 1.3134/1.2895/1.2615/1.2376, triple point y = 0.730–0.735. DMR foot 2.788, stem 2.743–2.766, incident 3.047–3.049. Riemann shocks 0.370–0.374 and 0.299–0.301. The detected frames agree with the hand-measured frames of the pass-1 paper review to within 1 px. |
| `stencil_diagnostics.py` (48 and 300) | Every entry of `tab:stencils` and the caption matches. So do the text values 5.7/16.7/72.9 %, 6.2/16.9 %, 5.02/18.75 % and 0.39/4.71 %. |
| `aligned_flux_diagnostics.py`, `fallback_positivity.py` | Both give 1797/20000 = 9.0 % (degree 3, geometric); aligned gives 0. |
| `make_epd_figure_light.py`, `make_epd_figure_addendum.py` | Byte-identical to `paper/figures/epd_rules_light.tex` and `addendum/figures/epd_rules_addendum.tex`. |
| `ho_defect_bloch.py 1 8,16,32 2,3,4 64 … geometric,aligned merge,insert,shift` | All 54 records equal to the committed `ho_defect_bloch_1d*.jsonl` (αh to 1e-6 relative, Kreiss to 1e-6). Script: `compare_defect_bloch.py`. |
| `ho_make_tables.py` | Regenerates all `stability/tables/*.tex` with no diff. The ∞ in `ho_random.tex` is justified: cloud n = 200, seed 0 has αh = 0.95. |
| `certify_K2_1d.py` (default) and with `10` | Passes for n ≤ 9, and reports the failure at P₁₀,₁. |
| `latexmk -pdf` in a copy of `paper/`, `addendum/`, `stability/` | All three exit 0, with no undefined or multiply defined references. `pdftotext` of each matches the committed PDF. |
| SSPRK(5,4) elimination, `ssprk54_stagevalues.py` | C = 1.50818. Coefficients 0.5172 / 0.1627 / 0.3409 / −0.0208 from the unrounded tableau, and 0.5173 from the rounded table, as stated. |
| `aidecl lint` | Exit 0 (205/205). |

**Not run:** the Lean build (no Lean toolchain here; only comments and `STABILITY.md` changed), the FV runs behind the "one fix at h = 1/160" statement, and the HyperCloud runs.

**Paper numbers checked against `results/reports/2026-10-29-rerun-078-tables.md`:**
- 57 + 3 runs.
- Global minimum p = 4.775e-3 (step, K = 3, k_div = K, EPD1).
- min p ≥ 0.2497 for k_div = 2 with EPD2.
- Riemann minimum 0.01775, which is 38.8 % below 0.029.
- Aligned vs geometric within 4.1 %.
- Step counts 13.5–13.7k, 13.5k (RK2MUSCL2), 13.1k (RK2MUSCL1) and 40.4–40.9k.
- Sod L1 orders 0.87–1.06.
- 2-D "5 to 30 times" at N = 1000: 4.9–31.7.

## Fixes verified

**Paper (`main_light.tex`).** P1/S4 (`:248`), S1 (`:263`), `:285`, `:330`, `:332`, P7/S2 (`:394`), P10, `:418`, `:563`, P4–P6 (`:686`), P3 (`:756`), P2/E1 (`tab:steppos`, `:784`, triple point) and P12 (Lean removed, Opus 5.5 for the tables) are all correct.
- The values in `tab:steppos` round the script output correctly. The claim "within 0.01 of the finest reference" holds (0.30–0.31 vs 0.31, 0.58–0.59 vs 0.59).
- The PR #11 change at `:246` ("more than 1.5 times") agrees with the addendum's `|N(i)| > 1.5(B_k+1)`.

**Addendum.**
- A1/E3: three rules.
- A2: rem:mood(iv).
- A3/A4/S8: rem:lean. The restrictions listed match the Lean signatures: `hspos`, `hlam`, `hSO` and `hone` in `Positivity.lean` and `Time.lean`.
- A5: rem:stagevalues. The new argument is correct. For FE, RK2 and RK3, every canonical row is a combination of Uⁿ and W_{k−1} only. A particle that fails the stage-value check at order one therefore has W_{k−1,i} ∈ 𝒢 by Prop 5.7, and Y_{k,i} ∈ 𝒢 follows by convexity.
- A6: the conservation remark. The logic is fine; see the minor note M4.
- A7: Cor 6.4.
- A8, S7: Prop 5.7 and (H4).
- The minors: B defined, Lemma 4.1 wording, the per-stage operator in Lemma 6.1, "the draft", and the date.

**Stability note.**
- S1: the fix in `ho_common.bloch_symbols` / `ho_defect_bloch.py` is correct. h = 1/(3m) is now the lattice spacing for merge and insert cells. 2-D cells are unaffected, because round(√(m²±1)) = m.
- New merge and insert K = 2 values: 1.6e-6 … 1.1e-9 and 2.6e-6 … 1.4e-8. The rate ≈ m⁻² for m ≥ 16 and the bound res ≳ ϱ⁻² follow.
- Insert K = 3 Kreiss constant 1.10 and `tab:defectbloch` (new third digits) match the data.
- F1/S2: ∞ in `tab:random`.
- Cor 8.8(i): the threshold now matches the proof (C₀e^{−cϱ} ≤ 2 min(c_W,1) g₋ h).
- S6: verified from the data.
  - K_V − 1 is at most 9e-5 (1-D, A = 0.15) and 4.8e-4 (2-D).
  - ω_V reaches 4.5e-4.
  - The K = 3 residual at ϱ = 16 is 7.9e-11 … 5.0e-9, and at most 1.07e-6 at ϱ = 12.
  - "Extrapolated" is stated.
- The AI declaration now calls the Lean formalization partial.

**Scripts and code.**
- `frames.py`-based detection works on all three figures.
- The EPD paths are fixed.
- `stencil_diagnostics.sign_mismatch` is shared, and the 300×300 rows are printed. `tot += D` replaces `tot += 2`, which is the same in 2-D.
- The Monte Carlo scripts share one function and one seed.
- `fv.py` usage: the docstring matches `sys.argv` handling, the limiter and flux codes match `lim()` / `hllc()`, and the output tag is right.
- `tst2.py` input is documented, and the `ho_defect_cert.py` docstring sign is fixed.
- `certify_K2_1d.py` defaults to 9, and the Sod report says 0.87.

**Lean docs.**
- The `STABILITY.md` relabels are consistent. I recounted the 30 rows: 2 Checked / 7 Checked, hyp. / 19 Partial / 2 Not done, as stated.
- `AxiomCheck.lean` only changed a comment.

## New findings

### N1 (should-fix): the K = 4 aligned insert array is now weakly unstable, but the note says α = 0

The corrected data in `stability/data/ho_defect_bloch_1d_insert_shift.jsonl` give, for insert defects with K = 4 and the aligned orientation:

| m | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| αh, after the fix | 3.7e-7 | 7.0e-8 | 1.1e-8 | 1.6e-9 |
| αh, at `a6edcc9` (wrong h) | 8e-17 | −1e-17 | −1e-16 | 3e-16 |

This is the same kind of weak instability as the aligned shift array (6.6e-7 … 1.3e-9), decaying about like m^−2.5 to m^−3. I reproduced it with the fixed script (`compare_defect_bloch.py`). The geometric K = 4 insert array is still zero to round-off. The text was not updated:

- `stability_combined.tex:1150`, `obs:defectbloch(ii)`: "For K=3 (all types) and K=4 (merge, insert) α=0 to round-off". Insert is true only for the geometric orientation.
- `:1151`, `obs:defectbloch(iii)`: names only the shift defect as the weakly unstable K = 4 aligned case.
- `:768`, after Cor 8.8, says the residuals "stall … for K=4 aligned at insert defects". `:169` (summary table) says "not for K=4 aligned at shift defects (weakly unstable arrays) and insert defects, where it stalls". `:143` says the residuals rule out decay "for … K=4 aligned (shift)". By the argument of (i), the residual for this type must satisfy res ≳ c ϱ^−(2.5…3), so it is now *ruled out*, not merely stalling. That agrees with the stall near 2–5·10⁻⁸ in `obs:cert`.
- `CHANGES.md` says "Signs and conclusions are unchanged". For this one cell the sign changed.

Fix: say "K = 4 (merge; insert with the geometric orientation)" in (ii). Add the insert array to (iii) with its αh values. Then change "stall" to "rule out" for K = 4 aligned insert at `:143`, `:169` and `:768`.

### N2 (should-fix): paper `:620`, the K = 5 explanation still does not match the strict rule

The text reads: "the degree-five derivative fit has six unknowns … and therefore requires 1.5·6 = 9 neighbours; at θ = 0.4 and κ = 5.5 some stencils have fewer, fall back to degree four …".

`neighbours_1d.py` (2·10⁵ particles) gives at θ = 0.4 a minimum of exactly 9 neighbours (10.8 % of particles), and never fewer. At θ = 0.2 every particle has 10. Losing both ±5h neighbours would need δ₅ − δ₋₅ > 1.0h, but |δ| ≤ 0.4h.

So the mechanism is right only with the strict rule of `:246` (as of PR #11), and the wording is wrong in both places:
- the fit requires *more than* 9 neighbours;
- the stencils that fall back have *exactly* 9.

Suggested text: "… therefore requires more than 1.5·6 = 9 neighbours; at θ = 0.4 and κ = 5.5 about 11 % of the stencils have exactly nine, fall back to degree four …".

Two related edits:
- `CHANGES.md`, "Follow-up of 5 Nov 2026 (evening)", says the sentence "stands as written". It should say it needs this edit.
- Open item 1 should be closed or reworded.

`:246` "k = 5 needs about κ ≥ 5.5 in one dimension" remains fine for the 0.2h clouds of the paper.

### Minor

- **M1, paper `:512`.** "errors at the finest resolution that are 5 to 30 times smaller than with κ = 5.5". This holds in 2-D (4.9–31.7). The sentence also covers 1-D lattices, where K = 4 gives 2.06e-8 / 4.94e-10 = 42×. The pass-1 review suggested "in two dimensions". The fix added only "at the finest resolution". (`:410` already says "two-dimensional lattices" and is fine.)
- **M2, paper AI declaration (`:890`).** The list of supplementary material no longer mentions Lean. The repository still ships `lean/`, and the addendum (`rem:lean`) and the stability note (AI declaration) both point to it. This is fine if Lean is deliberately not part of the paper's supplement. Otherwise mention it as "a partial Lean formalization". Pascal's call.
- **M3, `CHANGES.md`.** The stencil row says "unchanged values". The equal-volume mixed-pair value changed from 72.8 to 72.9 %, as the paper section notes, so the row is only slightly imprecise. Several findings of the code reviews are neither fixed nor listed under "Open":
  - code pass 2: F3 (rp3 triple points in `reference_solutions.md`), F5, S3 (SDP status unchecked, 13 `optimal_inaccurate` records), S4, S7–S9;
  - code pass 1: F2, F6, F7, F9, FV2, FV3, R1.

  None affects a published number. Listing them as deferred would make the open list complete.
- **M4, addendum, conservation remark (`:388`).** "Together with the closure Σ_j S_ij = 0 …, (scheme) can always be written as V_i dU_i/dt = −Σ_j S_ij·F*_ij by the definition of S_ij". The FV form does not need the closure. The closure is what makes it consistent (constants preserved). Wording only.
- **M5, `scripts/figure_measurements/frames.py` docstring.** It says a frame line has "more than half (30 %)" dark pixels. The code uses 50 % for rows and 30 % for columns.
- **M6, `tab:steppos`.** Bow 0.3045 → 0.30 and 0.3059 → 0.31, and stem 0.5823 → 0.58 and 0.5851 → 0.59, differ by 1–4 px (≈ 0.0014 per px). This is correct rounding, but the table shows 0.01 differences that the text rightly calls "within 0.005". This is acceptable; three decimals would avoid the apparent contradiction.

## Recommended declarations (G / A); H is Pascal's

| Files | G | A | Note |
|---|---|---|---|
| `scripts/figure_measurements/{steppos,dmrpos,clainpos2,frames}.py`, `scripts/make_epd_figure*.py`, `scripts/stencil_diagnostics.py`, `scripts/fallback_positivity*.py`, `scripts/aligned_flux_diagnostics.py` | G3 | **A2** | All rerun, outputs match. M5 is a docstring nit. |
| `fv_reference/fv.py`, `tst2.py`, `reference_solutions.md`, `README.md` | G3 (README G2 as declared) | **A2** | Documentation checked against the code. The "one fix" claim was not rerun. |
| `stability/scripts/{ho_common,ho_defect_bloch,ho_defect_cert,ho_make_tables,certify_K2_1d}.py`, `stability/data/ho_defect_bloch_1d*.jsonl`, `stability/tables/{ho_defect_bloch,ho_random}.tex` | G3 | **A2** | Regenerated and identical. |
| `results/reports/2026-10-29-sod1d.md` | G3 | **A2** | |
| `lean/STABILITY.md`, `lean/MeshfreeAddendum/AxiomCheck.lean` | G3 | **A2** | Docs and comments only. Lean not built. |
| `addendum/math_addendum.tex` / `.pdf` | G3 | **A2** | No new errors. M4 is wording. |
| `paper/main_light.tex` / `.pdf` (at 627fab6) | G2 | **A2** for the reviewed state | N2 and M1 should be fixed. The edited file then falls back to A1 until the edit is checked. |
| `stability/stability_combined.tex` / `.pdf` | G3 | **A2** for the reviewed state | N1 should be fixed, with the same fallback rule. |
| `CHANGES.md` | G2 | A2 | With the corrections of N1, N2 and M3. |

No reviewed file needs A3. A3 would require a reviewer of a different model family.
