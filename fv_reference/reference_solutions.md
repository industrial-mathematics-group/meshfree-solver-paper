# Reference values for the shock problems (double Mach reflection, Mach 3 step, 2-D Riemann configuration 3, Sod)

All problems use gamma = 1.4. The published studies of these problems (Woodward and Colella; Cockburn and Shu;
Kurganov and Tadmor; Liska and Wendroff; Kemm; Vevek, Zang and New) show the solutions as contour plots and give
no wave positions as numbers, and several state that no exact or reference solution is known. The reference values
below are therefore derived from shock relations where possible and otherwise computed with the finite-volume code
in this folder. Values marked "FV" are our own computations, not literature values.

## Method of the FV reference computations

- Cell-centred finite volumes on a uniform Cartesian grid (`fv.py`, Numba).
- MUSCL reconstruction of (rho, u, v, p) with the MC limiter; first-order fallback if a face value is not positive.
- HLLC flux with Einfeldt-Roe wave-speed estimates.
- SSP-RK3, CFL 0.4.
- An a posteriori first-order fallback on the faces of cells that would become non-admissible. Of the runs listed
  here only the step run at h = 1/160 triggers it (one fix); the step runs at 1/40 and 1/80 and the DMR and Riemann
  runs report no fixes and stay admissible without it (no NaN, minimum density and pressure equal to the
  smallest initial state).
- Solid walls by mirror cells, two ghost layers. The step is a masked solid block with mirrored stencil cells.
- DMR top boundary: the exact moving shock state is evaluated at the ghost-cell centres.

Wave positions are the crossing of the mean of the two adjacent plateau values (`analyze.py`), the same rule as in
the paper. The exact plane- and oblique-shock relations used as checks are in `rh.py`, `tst.py` and `tst2.py`.

## 1. Double Mach reflection (Woodward-Colella setup, t = 0.2)

**Incident shock at the top boundary (exact).** x_s(y, t) = 1/6 + (y + 20t)/sqrt(3). At y = 1, t = 0.2:
x_s = 3.0534; at the centre of the top particle row, y = 1 - h/2 with h = 1/450: 3.0528.

**Three-shock theory** (`tst.py`, `tst2.py`). Incident Mach number 10, wedge angle 30 degrees; the triple point
moves on a straight line through (1/6, 0) at angle chi to the wall.
- With the classical closure (straight Mach stem normal to the wall): chi = 7.73 degrees, triple point at
  (2.673, 0.340) at t = 0.2. The post-shock state rho = 8.000, p = 116.5 is reproduced.
- The computed solutions do not satisfy this closure: the stem is curved and leans back by 3-4 degrees at the
  triple point. For chi = 10.0 degrees, three-shock theory requires the stem to meet the wall direction at
  93.1 degrees; the FV runs give 93.4-94.6 degrees. The theory gives rho = 11.5 between the reflected shock and the
  slip line; the FV runs give 11.1-11.7. The self-consistent value is chi of about 10 degrees.

**FV runs** on [0, 3.2] x [0, 1] with the paper's boundary conditions.

| quantity (t = 0.2) | h = 1/120 | h = 1/240 | h = 1/480 | status |
|---|---|---|---|---|
| Primary triple point (x, y) | (2.740, 0.458) | (2.737, 0.453) | (2.739, 0.455) | converged, (2.738 ± 0.002, 0.455 ± 0.004) |
| Triple-point path angle chi from (1/6, 0) | 10.1° | 10.0° | 10.0° | converged |
| Mach stem at y = 0.3 | 2.7485 | 2.7490 | 2.7501 | converged, 2.750 |
| Mach stem at y = 0.2 | 2.7575 | 2.7587 | 2.7618 | nearly converged, about 2.76 |
| Mach stem at y = 0.1 | 2.769 | 2.775 | 2.783 | not converged |
| Mach stem foot at the wall | 2.789 | 2.802 | 2.814 | not converged (+0.013 per refinement) |
| Kink of the reflected shock | (2.210, 0.396) | (2.208, 0.392) | (2.200, 0.392) | converged, (2.20-2.21, 0.39) |
| Wall-jet vortex centre | (2.56, 0.07) | (2.62, 0.07) | (2.64, 0.07) | moves downstream under refinement |
| Incident shock in the top row | 3.0543 | 3.0541 | 3.0537 | exact 3.051-3.053 |

The forward bend of the Mach stem near the wall, where the wall jet runs into its foot, is a feature of the
inviscid solution and grows under refinement, so the position of the foot is not a converged quantity.

**Self-similarity check.** A run with h = 1/480 to t = 0.1 has the resolution of the h = 1/240 run at t = 0.2 in
similarity variables (xi, eta) = ((x - 1/6)/t, y/t). It gives: foot 13.171 vs 13.175; triple point
(12.853, 2.262) vs (12.853, 2.263); kink (10.193, 1.959) vs (10.204, 1.958); vortex (12.26, 0.34) vs (12.26, 0.34).
The solution with this boundary treatment is self-similar to plotting accuracy.

**Comparison with Kuhl et al.** (Mach 10 reflection on a 30 degree wedge, LBL report A119): their ratio of triple
point height to Mach stem distance, 0.72/4.29 = 0.168, compares with 0.171-0.173 from the FV runs; their stagnation
point ratio 0.816 corresponds to x = 2.32, where the slip line reaches the wall in the FV runs (2.32-2.33). This is
corroboration only, since the gas model of that study was not verified.

## 2. Mach 3 step (Woodward-Colella setup, t = 4, no corner treatment)

The flow is still unsteady at t = 4 and becomes steady at about t = 12 (Woodward and Colella), so there is no
steady-state or analytic value. Woodward and Colella report two Mach reflections of the bow shock at t = 4 and
an upper Mach stem directly above the step. Cockburn and Shu (1998) compute without a corner treatment and observe
an entropy layer and a small Mach stem on the step that shrink under refinement.

FV runs: rows y = 0.05, 0.95 and 0.215. "No fix" is the setup of the paper; "WC-type fix" resets entropy and total
enthalpy of the three cells at the corner to those of the cell left of and below the corner, to show how much the
corner matters.

| quantity (t = 4) | h | no fix | WC-type fix |
|---|---|---|---|
| bow shock at y = 0.05 | 1/40 | 0.311 | 0.307 |
| | 1/80 | 0.312 | 0.312 |
| | 1/160 | 0.309 | 0.311 |
| Mach stem at y = 0.95 | 1/40 | 0.621 | 0.627 |
| | 1/80 | 0.602 | 0.603 |
| | 1/160 | 0.593 | 0.594 |
| triple point at the upper wall, y | 1/80, 1/160 | 0.73, 0.77 | 0.73, 0.77 |
| shock on the top of the step at y = 0.215 | 1/40 | 1.207 | 1.385 |
| | 1/80 | 1.237 | 1.364 |
| | 1/160 | 1.282 | 1.342 |

- The bow shock lies at 0.31 at all resolutions, independent of the corner treatment.
- The Mach stem converges from the right (0.62, 0.60, 0.59); first-order extrapolation gives about 0.585.
- The reflection on the step depends on the corner: without the fix it is a small Mach reflection on the entropy
  layer that moves downstream under refinement, with the fix a regular reflection that moves upstream. The
  converged position lies between 1.28 and 1.34. Without a corner treatment, a reflection further upstream
  indicates a thicker entropy layer.

## 3. 2-D Riemann problem, configuration 3 (t = 0.3)

**Plane shocks (Rankine-Hugoniot, `rh.py`).**

| shock | speed from mass / momentum / energy flux | position at t = 0.3 |
|---|---|---|
| UL to UR (and LR to UR) | -0.66338 / -0.66329 / -0.66330 | 0.3010 |
| LL to LR (and LL to UL) | -0.42208 / -0.42233 / -0.42180 | 0.3734 |

The speeds differ in the fourth digit because the tabulated states are rounded to four digits. The FV runs give
0.3009 and 0.3733 at 800².

Liska and Wendroff (2003) state that exact solutions are not known for this problem and report start-up artefacts
on two segments of the initial discontinuities.

**FV runs** with transmissive boundaries (symmetric to machine precision, max |rho - rho^T| = 8e-13).

| quantity (t = 0.3) | 400² | 800² | status |
|---|---|---|---|
| Triple points at the end of the plane shock y = 0.373 | x = 0.229 | x = 0.228 | converged, (0.228, 0.373) and mirror |
| Upper triple points on the UR shocks | (0.312, 0.473) | (0.312, 0.473) | converged to about 0.003, and mirror |
| UR shock near the interaction (y = 0.48-0.50) | x = 0.311 | x = 0.312 | bends from 0.301 to 0.312 |
| Curved shock on the diagonal x = y | 0.293 | 0.289 | about 0.287 ± 0.003 |
| Jet cap on the diagonal (density drop from about 1.6 to 1.49) | 0.499 | 0.508 | not converged, moves outward |
| Maximum density and location | 1.78 at x = y = 0.429 | 1.75 at x = y = 0.428 | converged, 1.75-1.78 at (0.43, 0.43) |

The density maximum next to the jet is part of the solution: gas of the upper right state compressed by the
interaction.

## 4. Sod shock tube (t = 0.2, x0 = 0)

Exact Riemann solution: p* = 0.30313, u* = 0.92745, rho*_L = 0.42632, rho*_R = 0.26557; rarefaction head -0.2366,
tail -0.0141; contact 0.1855; shock 0.3504.

## Limitations

The non-converged quantities (the foot of the Mach stem, the wall-jet vortex and the jet cap) would need a
converged high-order reference, for example WENO5 at h = 1/960 or adaptive mesh refinement.
