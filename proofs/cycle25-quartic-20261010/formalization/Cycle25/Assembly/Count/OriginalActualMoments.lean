import Cycle25.Assembly.Count.OriginalCertifiedMoments
import Cycle25.Assembly.Count.PlainInput
import Cycle25.Assembly.Mesh
import Cycle25.Assembly.Count.Parameters

namespace OAI.SevenEighths.Cycle25ProbeFinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open Cycle25ProbeDetectorPlainMarkedFineField

/-- Actual physical source moments from the completed energy endpoint, on the
same mesh used by the physical numerator. -/
theorem weighted_actual_old_source_moments {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤Cycle25.sourceMesh D.t/200) :
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        old_sourceMomentBound F counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle25ProbeFinalAssemblyCertifiedBands.old_source_moments F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta)
end
end OAI.SevenEighths.Cycle25ProbeFinalAssembly
