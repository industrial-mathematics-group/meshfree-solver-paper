# Lean formalization of `math_addendum.tex`

Lean 4 (v4.35.0) + Mathlib (tag `v4.35.0`) formalization of the definitions, lemmas and
propositions of the mathematical addendum *Meshfree MUSCL schemes with a posteriori order
detection: exactness, conservation and admissibility* (HyperCloudCore.jl 0.7.8).
The stability note `stability/stability_combined.tex` (Part I) is formalized in the
second library `MeshfreeStability` of this project; see [STABILITY.md](STABILITY.md).

## Status

`lake build` succeeds with **no `sorry`, no `admit` and no extra axioms**.
`MeshfreeAddendum/AxiomCheck.lean` prints the axioms of 42 main results; each one depends only
on `propext`, `Classical.choice` and `Quot.sound`, Lean's standard axioms.

"Checked" below means that Lean has verified the stated theorem. Where the Lean statement is
weaker than the paper, or takes something as a hypothesis, the column "What is formalized"
says so.

## Building

```
lake exe cache get   # needs network access to cache.mathlib.org
lake build
lake env lean MeshfreeAddendum/AxiomCheck.lean
lake env lean MeshfreeStability/AxiomCheck.lean
```
Without the cache, `lake build` compiles the needed part of Mathlib, about 2,570 modules (about 2,900 Lake jobs in total).

## Modelling choices (apply throughout)

* **Unregularized fits.** Weights are defined with the exact inverse of the moment matrix.
  Tikhonov-regularized fits (Remark 1.1(i), Remark 3.2) are not modelled, and none of the
  reproduction or zero-row-sum results apply to them. This is the "approximate equality"
  case of the paper, which is left out on purpose.
* **Polynomials** `Π_q` are finite combinations of Taylor monomials `y^α/α!` with `|α| ≤ q`
  (`Poly D q`). Unisolvency (Def. 3.1) is stated for coefficient vectors in this basis
  (`UnisolventAt`), the usual identification of a polynomial with its coefficients.
* **Partial derivatives** are analytic: `pd g z d` is the derivative of `t ↦ g(z + t e_d)`
  at `0`. `pd_poly` proves that for polynomials this is the `e_d` Taylor coefficient.
* **One particle** is described by a finite neighbour type `J`, offsets `x : J → ℝ^D` and
  kernel weights `w`. The global cloud, ghost layer and boundary operator appear only where a
  statement needs them (conservation, Theorem 6.3).
* **States** live in an arbitrary real vector space with a convex admissible set `G`. The Euler
  equations are a concrete instance (`Euler.State D = ℝ × ℝ^D × ℝ`).

## Statement-by-statement status

| Addendum | Lean name(s) | What is formalized | Status |
|---|---|---|---|
| §2.1 convexity of the Euler admissible set | `Euler.convex_Adm` | full statement | checked |
| Def. 3.1 unisolvency | `Unisolvent`, `UnisolventAt` | coefficient form | definition |
| §3.1 reconstruction fit and reproduction | `recon`, `recon_reproduces`, `unisolvent_reconφ`, `lsCoeff_minimizes` | reproduction for unregularized fits; the formula is the least-squares minimizer; `Π_r`-unisolvency implies invertibility of `N_i` | checked (invertibility proved, not positive definiteness) |
| eq. (3.2) `eq:cij` derivative weights | `divWeight`, `lsWeight` | definition | definition |
| Lemma 3.3 (i), (ii), (iii) | `divWeight_reproduces`, `divWeight_sum_eq_zero`, `divWeight_dilate` | full statements (dilation for any `θ ≠ 0`) | checked |
| Remark 3.4 (constant term) | — | not formalized (remark) | — |
| Lemma 3.5 weight bound | `divWeight_abs_le`, `sum_abs_le_of_abs_le` | Assumption 2.1(ii) and `C_κ` written as bounds on sums of squares (Euclidean norms); bounds `C_N C_κ/h` and `D N_max C_N C_κ/h` | checked |
| Lemma 3.7 (i), (ii) parity | `divWeight_antisymm`, `divWeight_reproduces_succ_of_odd` | full statements (the involution may be any permutation) | checked |
| Lemma 3.7 (iii) | `parity_fails_even`, `parity_fails_even'` | the counterexample `D=1`, `q=2`, offsets `±1, ±2`, unit weights, `g=y³`: the sum is `17/5 ≠ 0`. That this stencil is `UnisolventAt 2` and centrally symmetric (what makes it a counterexample to the lemma's hypotheses) is true but not proved in Lean | checked (computation) |
| Corollary 3.8 derivative error | `derivative_error_le` | algebraic core: exactness on `Π_m` + `∑|c| ≤ A/h` + Taylor remainder bound ⇒ error `≤ A C κ^{m+1} h^m`. **The Taylor remainder bound is a hypothesis**; multivariate Taylor's theorem is not formalized. Since that bound is the analytic content of the corollary, the addendum's Remark 1.2 lists it as "checked with a hypothesis" | checked (with hypothesis) |
| Definition 3.9 `q(k)` | `qdiv`, `qdiv_odd`, `qdiv_ge`, `qdiv_le_of_odd`, `qdiv_of_even`, `qdiv_of_odd` | full: smallest odd degree `≥ k−1` | checked |
| Remark 3.10 safeguards | — | implementation remark, not formalized | — |
| eq. `eq:rusanov` Rusanov flux, orientations | `rusanov`, `geomSign`, `alignedFluxOrientation`, `IsAligned` | definitions | definition |
| Lemma 4.1 symmetric fluxes | `rusanov_swap`, `symmetric_interface_flux`, `geometric_orientation_antisymm`, `aligned_orientation_antisymm`, `aligned_orientation_zero` | full | checked |
| Prop. 4.2 exactness | `exactness_linear` (+ `recon_reproduces`) | conclusion `L_i = −∑ A_d ∂_d u(x_i)` for any `σ`, `s`. **Interface states `U_ij = U_ji = u(m_ij)` enter as hypotheses**; they follow from `recon_reproduces` applied at `i` and at each neighbour, but the two are not combined into one theorem; using it at a neighbour also needs the translation invariance of `Poly D q` (the reconstruction at `j` is in local coordinates around `x_j`), which is not proved | checked (with hypotheses) |
| Prop. 4.3 lattice consistency | `lattice_flux_parity`, `lattice_flux_cancel` | **only the algebraic steps**: evenness of the leading flux error `G_d` and its cancellation against odd weights. The `O(h^{k+1})` expansions of reconstruction errors and fluxes are not formalized | partial |
| Prop. 4.4 conservation balance | `ConsData.conservation_balance`, `bracket_symm` | full identity (pairs summed as ordered pairs with factor ½; `bracket_symm` makes this equal to the unordered sum) | checked |
| Prop. 4.4 (i), (ii), (iii) | `eDef_geometric`, `eDef_aligned`, `eDef_convention`, `eDef_convention_unbounded` | full, plus a numerical example for "not bounded in general" | checked |
| local conservation after Prop. 4.4 | `local_conservation`, `defects_vanish_of_antisymm` | "if" direction, for antisymmetric orientations; the `c = 0` convention on geometric edges with `x_d = 0`, which the text also allows, is not covered | checked (antisymmetric case) |
| Lemma 5.1 | `Euler.lf_state_admissible` | full, Euler in `D` dimensions | checked |
| Prop. 5.2 positivity | `first_order_update_admissible` | full, with condition (b) as `σc = |c|` (see note 1) | checked |
| Cor. 5.3 aligned orientation | `aligned_update_admissible`, `scalar_led` | vector statement and the scalar LED statement | checked |
| Remarks 5.4 and 5.5 | — | implementation remarks, not formalized | — |
| eq. `eq:epd` EPD rules | `EPD`, `epdOrder`, `cnb` | definitions (StrictEPD0 omitted, as in the addendum) | definition |
| Proposition 5.6 fallback | `fallback_orders`, `fallback_all_order_one`, `truncRecon_one`, `epd0_not_fallback`, `epd0_state_not_constant` | full, including EPD0 counterexamples for the order and the state | checked |
| Proposition 5.7 local admissibility | `local_admissibility_order_one` | full for one particle. `local_admissibility_order_one` takes the interface orders as hypothesis `hord : kij = kji = 1`; `local_admissibility_order_one_epd` composes it with `fallback_orders` / `fallback_all_order_one`, so the orders are those of EPD1/EPD2 (or any rule when all orders are `≤ 1`) on the neighbour graph | checked |
| eq. `eq:canonical`, Lemma 6.1 Shu–Osher form | `soAlpha`, `soV`, `soAlpha_strictLower`, `soV_add_sum`, `inv_one_add_eq`, `shuOsher_form` | full (for any `r ≠ 0`) | checked |
| SSP coefficient, RK1/RK2/RK3 canonical forms | `rk1_canonical`, `rk2_canonical`, `rk3_canonical` | exact canonical forms at `r=1` and non-negativity. **Maximality (`C = 1`) is not proved**, nor the values for Ralston (`½`) and RK4 (`0`) | partial |
| Table 1, SSPRK(5,4) | — | numerical; **not formalized**, used only as an assumption | assumption |
| Remark 6.2 | `ssprk54_elimination`, `ssprk54_negative_coefficient` | exact elimination identity; the coefficient of `Uⁿ` is negative for every set of coefficients within `±5·10⁻⁵` of Table 1 | checked (given Table 1) |
| Algorithm 1 MOOD checkpoint | `Checkpoint.run`, `Checkpoint.run_spec`, `Checkpoint.run_admissible` | the loop as a terminating function (termination proved). **Exact locality is a hypothesis** (`Checkpoint.Local`); the hop structure of the actual operator is not modelled | checked (with hypothesis) |
| Theorem 6.3 | `stagewise_mood_admissible`, `ssp_stages` | full induction over stages and checkpoints. Proposition 5.7 with (H1), (H2), (H4) enters as hypothesis `hone`, and the Shu–Osher relation of the stages as `hSO` (from `shuOsher_form`) | checked (with hypotheses) |
| Corollary 6.4 | `ssp_order_one` | full, with first-order admissibility of the substeps as hypothesis (Cor. 5.3) | checked (with hypothesis) |
| Remark 6.5 (i)–(v) | — | not formalized; (iii) is the approximate time-step case | — |

## Notes for the paper

Note 1 was incorporated into `math_addendum.tex` and `main_light.tex` on 2026-10-29, together with Remark 1.2 of the addendum, which summarizes this formalization.

1. **Prop. 5.2, condition (b).** With `σ ∈ {−1, 0, 1}`, condition (b), `σ c ≥ 0`, does not
   imply `c = σ|c|`, which the proof uses: `σ = 0` and `c ≠ 0` satisfy (b). The Lean version
   assumes `σ c = |c|`, which is equivalent to (b) plus "`σ ≠ 0` wherever `c ≠ 0`". Both
   orientations of the scheme satisfy the added clause `σ ≠ 0`: the geometric one never takes
   the value `0` (the convention gives `−1`), and the aligned one is `sign c`. The aligned
   orientation satisfies the whole condition; the geometric one violates `σ c ≥ 0` in general
   (addendum Remark 5.4(i)), which is why Cor. 5.3 uses the aligned one. Suggested wording:
   "(b) `σ_{ij,d} c^{(d)}_{ij} = |c^{(d)}_{ij}|`".
2. **Lemma 3.3 / §3.1.** The proofs only use that `N_i` is invertible. Lean proves this from
   unisolvency and `w > 0`. Positive definiteness is true but not needed.
3. **Lemma 3.7(ii).** Lean uses a shorter argument than the paper: with (i), the degree-`q+1`
   part is even and the weights are odd, so the sum vanishes directly. The paper's argument
   via `P a = a` is also correct.
4. **Lemma 6.1** holds for every `r ≠ 0`, not only `r > 0`.

## Files

* `MeshfreeAddendum/LeastSquares.lean`: abstract weighted least squares (Gram matrix,
  weights, reproduction, scaling, reflection)
* `MeshfreeAddendum/Taylor.lean`: multi-indices, Taylor monomials, `Π_q`, partial derivatives
* `MeshfreeAddendum/MLS.lean`: Section 3 (Remark 3.2, Lemmas 3.3, 3.5, 3.7, Corollary 3.8, Definition 3.9)
* `MeshfreeAddendum/Scheme.lean`: Section 4 (Lemma 4.1, Props. 4.2 to 4.4)
* `MeshfreeAddendum/Positivity.lean`: Section 5 (Euler, Lemma 5.1, Prop. 5.2, Cor. 5.3, Props. 5.6, 5.7)
* `MeshfreeAddendum/Time.lean`: Section 6 (Lemma 6.1, Algorithm 1, Theorem 6.3, Corollary 6.4)
* `MeshfreeAddendum/AxiomCheck.lean`: `#print axioms` for the main results
