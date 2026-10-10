import QRH.Detector.ActualOptimizedHigh
import QRH.Detector.LowNormalized
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource

namespace OAI
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.QRHFinalAssembly
open HeckeFamily ProbeFinalAssembly QRHParameters

theorem actual_optimized_low {gap:ℝ} {D:Parameters.HighData gap} (S:SourceData D)
    (loss:ℝ) (hloss:0<loss) (η:Character):
    optimizedNormalizedProbe S η=O[atTop](fun Z:ℝ=>Z^(QRH.C QRH.tightTheta+loss)) := by
  obtain ⟨C,hC,hb⟩:=ProbePhysical.original_normalized_compensatedPhysicalProbe_low_optimized
    S.modulus ⊤ le_top S.S S.exclusions S.maximal 1 2 1 loss (by norm_num) (by norm_num) hloss
    (optimizedLengths D) (optimizedLengths_pos D) (optimizedLengths_injective D)
    (optimizedLengths_sum D) (fun _=>S.w) (fun _=>S.smooth) (fun _=>S.compact)
    (fun _=>S.support) (fun _=>S.bounded) (fun _=>S.nonzero) S.W S.W
    1 2 1 2 (by norm_num) (by norm_num) S.complex_support S.complex_support
    S.real S.real S.nonnegative S.nonnegative S.complex_nonzero S.complex_nonzero η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z h
  simpa only [optimizedNormalizedProbe,SourceData.modulus] using h.2

end SevenEighths.QRHFinalAssembly
end
end OAI
