import MeshfreeAddendum

/-! Prints the axioms used by the main results. Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` should appear; `sorryAx` would
indicate an unfinished proof. -/

open Meshfree

#print axioms divWeight_reproduces
#print axioms divWeight_sum_eq_zero
#print axioms divWeight_dilate
#print axioms divWeight_abs_le
#print axioms sum_abs_le_of_abs_le
#print axioms divWeight_antisymm
#print axioms divWeight_reproduces_succ_of_odd
#print axioms parity_fails_even'
#print axioms derivative_error_le
#print axioms qdiv_le_of_odd
#print axioms rusanov_swap
#print axioms aligned_orientation_antisymm
#print axioms symmetric_interface_flux
#print axioms recon_reproduces
#print axioms exactness_linear
#print axioms lattice_flux_parity
#print axioms lattice_flux_cancel
#print axioms ConsData.conservation_balance
#print axioms ConsData.eDef_geometric
#print axioms ConsData.eDef_aligned
#print axioms ConsData.eDef_convention
#print axioms ConsData.local_conservation
#print axioms ConsData.defects_vanish_of_antisymm
#print axioms Euler.convex_Adm
#print axioms Euler.lf_state_admissible
#print axioms first_order_update_admissible
#print axioms aligned_update_admissible
#print axioms scalar_led
#print axioms fallback_orders
#print axioms fallback_all_order_one
#print axioms epd0_state_not_constant
#print axioms local_admissibility_order_one
#print axioms local_admissibility_order_one_epd
#print axioms soAlpha_strictLower
#print axioms shuOsher_form
#print axioms rk3_canonical
#print axioms rk2_canonical
#print axioms ssprk54_elimination
#print axioms ssprk54_negative_coefficient
#print axioms Checkpoint.run_admissible
#print axioms stagewise_mood_admissible
#print axioms ssp_order_one

/-- Non-vacuity: the hypotheses of `ssprk54_negative_coefficient` hold for the Table 1 values. -/
example : (0.2380 : ℝ) - 0.2874 * 0.4444 / 0.5556 - 0.1337 * 0.1781 / 0.8219 < 0 :=
  ssprk54_negative_coefficient 0.4444 0.1781 0.2380 0.5556 0.8219 0.2874 0.1337
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
