import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Count.BaselineMoments
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Low.Probe
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Transport.PrincipalSignal
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.Continuation
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical Cycle63DetectorCount PrincipalSignalComparison

def sourceProbe (D : BaselineData) (F : BaselineSourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  Cycle63Low.normalizedProbe F.modulus ⊤ F.S F.maximal D.length 1 2
    (fun _=>F.w) F.W F.W η

theorem sourceProbe_low (D : BaselineData) (F : BaselineSourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    sourceProbe D F η=O[atTop](fun Z : ℝ=>Z^(Assembly.signal Arithmetic.theta+loss)) := by
  have hh := Cycle63Low.normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss D.length D.slots_pos
    D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  exact hh

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|Arithmetic.theta<s.re} ∧
    (∀s : ℂ,Arithmetic.theta<s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    Transport.remainder_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6) (by norm_num) (by norm_num),
    fun s hs=>Transport.PrincipalSignal.sourceCorrection_bound η S hS s hs⟩

theorem fixed_source_contract (D : BaselineData) (F : BaselineSourceData D)
    (loss sigma : ℝ) (hloss : 0<loss)
    (herror : ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-sigma))) :
    WeightedQRH.PrimitiveProbeContract Arithmetic.theta Assembly.signalShift loss sigma := by
  intro η _
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  simpa only [Assembly.signal] using sourceProbe_low D F loss hloss η
end
end Cycle63.FinalAssembly

end Record1252270103Bootstrap.PR67
