/- Actual original moments on the fresh Target830 slots and finite count family. Apache-2.0. -/
import Candidate.Target830.Physical.SourceMoments
import Candidate.Target830.Physical.MomentGates

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical
noncomputable section
open scoped Classical
open Filter HeckeFamily

theorem actual_baseline_source_moments (D : BaselineData) (F : BaselineSourceData D)
    (counts : DetectorCount.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200)
    (haffine : ∀P : Count.Plane,InitialTransport.weighted_AffineFineInputAt P F) :
    ∀η:Character,∃J:ℝ,0≤J ∧ ∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤1→
      ∀ᶠZ:ℝ in atTop,SourceMomentBound D (baselineSource D F) counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact SourceMoments.weighted_actual_source_moments_A F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hβ hκβ counts hfine haffine
end
end OAI.SevenEighths.Target830.Physical
#print axioms OAI.SevenEighths.Target830.Physical.actual_baseline_source_moments
