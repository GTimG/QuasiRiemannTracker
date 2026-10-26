/- The actual finite source recursion supplies the final weighted moment.
Copyright (c)2026 Zhongpai Gao. Native reductions by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootInitialHighSchedule
import Candidate.Research.RecursiveAffine.NativeRecursiveRootLow
import Candidate.Research.RecursiveAffine.RootLiteralBudget
import Candidate.Research.RecursiveAffine.RootWeightedMoment
import Candidate.Research.RecursiveAffine.Endpoint.RootMomentFactory

noncomputable local instance actualMomentRootLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153RootInitialAssembly
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap ComplexConjugate HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ProbePhysical CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily Cycle63InitialMass
open Cycle153SourceSchedule Cycle153Reachable Cycle153RootLowSchedule Cycle153RootInitialHigh
open Cycle153.RegionalSchedule

/-- The actual root moment required by both final detector and numerator.
All LOW/HIGH and counting inputs are supplied by the native finite source
proof. The seed normalization is proved at both actual endpoint callers. -/
theorem actual_weighted_root_initial {D : WeightedQRH.MomentData}
    (S : ProbeFinalAssembly.WeightedSourceData D)(eta : Character)
    (heta : eta.modulus ≤ Ideal.span {fixedBadMask})(hEta : excluded eta 1=eta)
    (eps meshUsed bPhi : ℝ)(heps : 0 < eps)(hmesh : 0 < meshUsed)
    (hmeshUsed : meshUsed ≤ rootMomentMesh eps)(hbPhi : 2 ≤ bPhi)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0 < C ∧∀ᶠZ : ℝ in atTop,
      Cycle153EndpointMoment.InitialAffineAt (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bPhi meshUsed (33/50) (33/50) 1 1 eps Z
        eta eta (weighted_sourceFixedIdeal S) degree Sd C :=by
  let W : ℝ→ℂ:=fun x=>conj (S.W x)
  have hW : ContDiff ℝ ∞ W:=HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤)
  have hWs : Function.support W⊆Set.Icc (1:ℝ) 2:=
    CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support S
  let Q:=weighted_sourceFixedIdeal S
  have hQM : Q ≤ S.modulus:=weighted_sourceFixedIdeal_le_modulus S
  have hQ0 : internalQ Q eta≠0:=internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) eta
  have hQt : internalQ Q eta≠⊤:=internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) eta
  have hQ72 : internalQ Q eta ≤ Ideal.span {(72:O)}:=inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S)
  let tau:=actualRecursiveRootTau S.modulus ⊤ le_top eta
  have htau : 0 < tau:=actualRecursiveRootTau_pos S.modulus ⊤ le_top eta
  obtain ⟨g,hmu,hdelta,hcut,hHigh⟩:=actual_initial_root_high_schedule (alpha:=Fin D.N)
    S.modulus ⊤ le_top W hW hWs hbeta hbetaHi eta heta hEta bPhi tau hbPhi htau
  have hmOriginal : meshUsed ≤ originalSlotMesh eps:=hmeshUsed.trans (rootMomentMesh_source eps)
  have hmLocal : meshUsed ≤ localSlotMesh eps:=by
    simpa only [div_one] using rebased_original_weight heps (U:=1) (by norm_num) hmOriginal
  have hmeshAmp : meshUsed < Cycle63.AffineLedger.amplifierFloor/2:=
    hmLocal.trans_lt (root_source_mesh_gates heps).1
  have hmeshCommon : meshUsed ≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8):=by
    rw [hmu]
    exact hmLocal.trans (root_source_mesh_gates heps).2.2.1
  have hmeshMarked : meshUsed ≤ Cycle63MarkedPlain.markedRawMesh*Cycle63MarkedPlain.markedCoreMin:=by
    have hm:=localSlotMesh_gates heps
    have hp:=(localSlotMesh_pos heps).le
    linarith only [hmLocal,hm.2.2.2.2,hp]
  have hmuActual : g.μ=geometryLossUnit 1 primitiveError:=hmu.trans root_native_mu.symm
  have hdeltaActual : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card (Fin D.N):ℝ)+2)) (Fintype.card (Fin D.N)):=by
    simpa only [nativeDriverRate,hmu] using hdelta
  have hreserve : 128*g.μ ≤ Cycle63.AffineLedger.lowReserve:=by
    rw [hmu]
    exact root_native_reserve
  have budget:=literal_root_budget_from_recursive_low (α:=Fin D.N) S.modulus ⊤ le_top
    fixedBadPrimes le_rfl W hW hWs hbeta hbetaHi g primitiveError meshUsed (eps/4) tau
    primitiveError_pos (by positivity) hmesh.le hmeshAmp hmuActual hdeltaActual hmeshCommon hmeshMarked hreserve
    eta eta Q hQM hQ0 hQt hQ72 bPhi
    (by
      intro Cs hCs Psi hPsi hpPsi T
      exact eventual_actual_recursive_root_low (alpha:=Fin D.N) le_top W hW hWs hbeta hbetaHi
        eta heta Q hQM hQ0 hQt hQ72 eps heps meshUsed hmesh.le hmOriginal g hmu hdelta hcut bPhi Cs hCs T)
    (by
      intro T
      obtain ⟨P,he,ht,SH,dh,KH,hKH,hs⟩:=hHigh T
      exact ⟨P,he,ht,SH,dh,KH,hKH,hs Q hQM hQ72⟩)
  exact weighted_root_initial_from_actual_budget S eta eps meshUsed bPhi tau
    (geometryLossUnit 1 primitiveError/64) heps hmesh hmeshUsed hbPhi htau
    (by rw [root_native_mu];exact div_pos nativeMu_pos (by norm_num)) hbeta hbetaHi budget

end
end OAI.SevenEighths.Cycle153RootInitialAssembly

namespace Cycle153Endpoint
noncomputable section
open OAI.SevenEighths.Cycle153RootInitialAssembly
/-- Constructed from the actual finite source proof, not an analytic axiom. -/
def actualRootMomentFactory : RootMomentFactory where
  mesh:=rootMomentMesh
  mesh_pos:=rootMomentMesh_pos
  moment:=actual_weighted_root_initial
end
end Cycle153Endpoint
#print axioms OAI.SevenEighths.Cycle153RootInitialAssembly.actual_weighted_root_initial
#print axioms Cycle153Endpoint.actualRootMomentFactory
