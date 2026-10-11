import LocalMoment.FiniteDeletionBins
import LocalMoment.UnmarkedDensity
import LocalMoment.BufferedSlot
import LocalMoment.RestrictedIncumbent
import LocalMoment.SixthRowMask
import LocalMoment.RawSixthDensity
import LocalMoment.UniformDensity
import LocalMoment.UnmarkedBatch

/-! These are verified components of the proposed local-moment source.
The full physical moment and tracker endpoint are deliberately absent. -/

#print axioms OAI.SevenEighths.LocalMoment.zeroMaximum_eq_of_mask
#print axioms OAI.SevenEighths.LocalMoment.count_from_unmarked_raw_moments
#print axioms OAI.SevenEighths.LocalMoment.natural_relative_slot_buffered_bound
#print axioms OAI.SevenEighths.LocalMoment.restricted_paid_incumbent
#print axioms OAI.SevenEighths.LocalMoment.sixthFrequency_zeroMaximum
#print axioms OAI.SevenEighths.LocalMoment.raw_density_from_free
#print axioms OAI.SevenEighths.LocalMoment.uniform_free_density_varying_of_eventually
#print axioms OAI.SevenEighths.LocalMoment.raw_density_uniform_exponent
#print axioms OAI.SevenEighths.LocalMoment.raw_density_from_eventual_free
#print axioms OAI.SevenEighths.LocalMoment.batch_count_from_unmarked_raw_moments
#print axioms OAI.SevenEighths.LocalMoment.unmarkedDensity_gt_one_sixth
#print axioms OAI.SevenEighths.LocalMoment.supportedRowRetraction_mem
