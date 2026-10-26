/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Nonnegative frequency coordinates follow from the actual nonzero encoded
lattice row and its norm bound, independently of the positive plain scales. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.LocalMoment.RawSixthDensity
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths LocalMoment HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical

theorem raw_frequency_norm_one_le (w:NonzeroFrequency) : 1≤rawFrequencyNorm w := by
  change (1:ℝ)≤((Ideal.span {w.val}).absNorm:ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr w.property))

theorem raw_frequency_exponent_nonnegative (Z q:ℝ)(hZ:1<Z)
    (w:NonzeroFrequency)(hbound:rawFrequencyNorm w≤Z^q) : 0≤q := by
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  simpa only [Real.rpow_zero] using (raw_frequency_norm_one_le w).trans hbound

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.raw_frequency_norm_one_le
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.raw_frequency_exponent_nonnegative
