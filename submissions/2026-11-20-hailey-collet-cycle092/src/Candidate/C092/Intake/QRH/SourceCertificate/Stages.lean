/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.Core

/-!
# Exact finite count of source cap contractions

This checks the two adjacent endpoint powers and proves minimality for all
previous natural indices. The conclusion is a fact about the rational cap
sequence; no source-estimate admission rule is assumed or concluded.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QRH.SourceCertificate

/-- The recovered source contraction takes exactly 2904 steps to cross its lower cap. -/
theorem source_stage_crossing :
    Y*H^2904 ≤ (369:ℚ)/1000 ∧ (369:ℚ)/1000 < Y*H^2903 := by
  decide +kernel

/-- Every earlier contraction stage remains strictly above the lower source cap. -/
theorem source_stage_minimal (n : ℕ) (hn : n < 2904) :
    (369:ℚ)/1000 < Y*H^n := by
  have hn' : n ≤ 2903 := by omega
  have hp : H^2903 ≤ H^n := pow_le_pow_of_le_one (by norm_num [H,u]) (by norm_num [H,u]) hn'
  have hY : (0:ℚ) ≤ Y := by norm_num [Y]
  exact lt_of_lt_of_le source_stage_crossing.2 (mul_le_mul_of_nonneg_left hp hY)

end QRH.SourceCertificate
