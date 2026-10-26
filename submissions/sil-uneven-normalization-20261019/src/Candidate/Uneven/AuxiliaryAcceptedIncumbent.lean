/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   This bridge depends only on the unchanged PR63 endpoint. -/
import Candidate.Target830.Source.RecordEndpoint
import Candidate.Uneven.AuxiliaryIncumbent

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.AuxiliaryLow

/-- The auxiliary source uses the preceding PR63 result, with no dependence
on the new seven-case count or the proposed improved endpoint. -/
theorem incumbent_kappa_bound :
    2 * HeckeZeroSupremum.beta - 1 ≤ incumbentKappa := by
  have h := Target830.Source.RecordEndpoint.beta_le_rational
  norm_num [incumbentKappa, Sil.Uneven.AuxiliarySource.kappa]
  linarith

end OAI.SevenEighths.AuxiliaryLow
