/- Literal unit of the SAME root common source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootCommonCallbacks
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearNormalization CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn Cycle63FinalCapacity Cycle63FinalLow
open Cycle63Moment Cycle153RegionalLow Cycle153ContinuationUnit Cycle153RootStep
open Cycle63FinalNatural Cycle63InitialMass
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
theorem canonical_root_common_unit (C : SourceContext (α:=alpha) M H)
    (s : Input alpha)(ch : Chain s)(chi : Character)(t : ℝ)
    (n : ℕ)(b omega xi reserve : ℝ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi b n)
    (B : actualAllocations (withHeight ch.first chi t).pools ch.E₂)
    (hn : commonScalar (withHeight ch.first chi t) ch.E₂ ch.R₂ B≠0) :
    let q:=commonContinuationChain s ch chi t B
    let gg:=commonContinuationGeometry g chi t B hn
    nativeUnit 1 C.globalBase (rootSourceAmp C.originalWeight) omega reserve xi q.C₁ gg.D₁
      gg.datum.C gg.datum.D gg.datum.inactive=
    secondNominal 1 C.globalBase (rootSourceAmp C.originalWeight) omega ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive+(reserve+xi/2) :=by
  dsimp only[nativeUnit,commonContinuationChain,commonContinuationGeometry,LiveMainGeometry.D₁]
  ring
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.canonical_root_common_unit
