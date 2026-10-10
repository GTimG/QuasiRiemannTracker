import WeightedQRH.MomentFinalAssemblyCertifiedBands
import WeightedQRH.MomentTerminalInput

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.ProbeFinalAssemblyCertifiedBands
open HeckeFamily ProbeFinalAssembly
open ProbeDetectorPlainMarkedFineField

/-- Genuine certified moment estimates for the new physical source.
There is no `HighData (beta-7/8)` and no hypothesis `7/8 < beta`. -/
theorem weighted_actual_source_moments {D : WeightedQRH.MomentData}
    (F : WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j, D.ell j ≤ weighted_detectorMesh D.t / 200) :
    ∃J:ℝ, 0 ≤ J ∧ ∀η:Character, ∃C:ℝ, 0 < C ∧
      ∀τ:ℝ, 0 < τ → τ ≤ 1 → ∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBound F counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨hp,hz⟩ := weighted_plain_inputs F (weighted_terminal_certificate F hbeta)
  exact weighted_source_moments F counts (weighted_detectorMesh D.t)
    (weighted_detectorMesh_pos D.t_pos) hfine hp hz

/-- The plain positive energy input is certified independently of class counting. -/
theorem weighted_actual_positive_fine_input {D : WeightedQRH.MomentData}
    (F : WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    weighted_PositiveFineSourceInput F (weighted_detectorMesh D.t) :=
  (weighted_plain_inputs F (weighted_terminal_certificate F hbeta)).1

end SevenEighths.ProbeFinalAssemblyCertifiedBands
end
end OAI
