/- A48 (AI-assisted, for liqsweep). WORK IN PROGRESS: this module contains an explicit `sorry`.
Apache 2.0; the Cycle61 source it imports is Hailey Collet's (tracker PR #42) with Zhongpai Gao's
parameter refinement (PR #43), unchanged. -/
import Candidate.Bundles.B192
import Candidate.CountAffine.Branch
import Candidate.CountAffine.Record

set_option autoImplicit false

namespace Cycle61.CountAffine.Assembly
open OAI.SevenEighths

/-- The record supremum bound beta <= 2187109/2500000 (h = 497/625, q0 = 67/100).

NOT YET FORMALIZED (explicit sorry). The mathematical argument: Collet's cycle61 proof with Gao's
constants, in which the detector count's plain witnesses of length m in [41/100, 264/625] are bounded by
Collet's interior affine moment (her Thm 2.2) instead of the 6-kappa plain moment. Steps still to be
formalized, in the order they enter:
* STEP (constants): propagate theta = 2187109/2500000, h = 497/625 through the Cycle61/Gao bundles
  (B000 constants, B024 / B060 derived reserves, coarse facts such as `h_interval`, which must be
  widened since 795/1000 < h; see `Record.h_above_gao_interval`). All Collet/Gao gates hold exactly
  (`Record.plain_window`, `slot_window`, `shift_gate`, `kappa_window`, `floor_gate`, `lower_row_gate`,
  `supply_gates`, `geometry_gates` are proved).
* STEP (count branch): the fiber/batch detector count with prover cut-off `tStar` and an
  `AffinePlainMoment` fiber field (gates 41/100 <= m <= 44/100, 17/500 <= sum w <= 1/25,
  2m + lambda*sum w <= B; shortened slot sets use the old moment since 2(264/625)+(9/2)(17/500) < 1).
  Its arithmetic core is proved: `Cycle61.CountAffine.affine_count_bound_of_branches` (Branch.lean),
  with the region side conditions in RegionFacts.lean. Remaining: the OAI fiber/batch plumbing
  (a copy of `count_from_raw_moments` / `balanced_adaptive_count_from_raw_moments` with the extra
  branch and the cut-off `if region then tStar else cutoff`), the new `countingR` and its
  antitonicity in p for the masked count transfer.
* STEP (Thm 2.2 instance for the count's characters): `Cycle61Moment.InitialAffineAt ... λ λ
  (weighted_sourceFixedIdeal F)` for every detector label character
  λ = sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label, via Collet's anchor-general
  chain (`actual_affine_main_uniform_paid` with a `NaturalRow λ 1` whose character is λ,
  `actual_affine_error_normalized_family`, `literal_affine_geometry_budget_of_main_error`,
  `literal_geometry_initial_affine`), then the energy comparison of
  `weighted_source_batch_marked_initial`.
* STEP (per-target height choice): the polynomial-height degree of these instances depends on the
  target η, so the height exponent τ must be chosen after η in `common_probe_of_chosen_finite_numerator`
  (single-η copies of `normalizedProbe_high_of_finite_nonfloor_numerator` and
  `fixed_numerator_of_cells`); `UniformCommonProbe` only needs ω, σ uniform.
* STEP (endpoint certificate): `Record.endpoint_certificate` (stated precisely, sorry). -/
theorem record_beta_le : HeckeZeroSupremum.beta ≤ (2187109 / 2500000 : ℝ) := by
  sorry

end Cycle61.CountAffine.Assembly
