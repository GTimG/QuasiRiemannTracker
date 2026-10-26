/- Actual prechosen LOW source metadata at the same reachable node.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.InnerCanonicalMetadataAtNode
import Candidate.Research.RecursiveAffine.InnerLowGridMetadata
import Candidate.Research.RecursiveAffine.NativeSelectedScalarThreshold

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153InnerLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle153RegionalLow Cycle153SourceUniform Cycle153SourceSchedule
open Cycle153TerminalSchedule Cycle153Reachable Cycle153ActualColumn Cycle153ActualSourceGates
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
variable (eps tau Bnorm : ℝ)(heps : 0<eps)(hB : 0≤Bnorm)(eta : Character)(Q : Ideal O)
variable (hQM : Q≤M)(hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(j : Fin 4)(hj : j.val<3)
variable (i : InnerGridIndex j)
variable (S : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
  eps tau Bnorm heps eta Q hQM hQ72 j i)

/-- The genuine scalar-source threshold uses the fixed original budget
and post rate. It is chosen before every moving context and rebase. -/
theorem eventual_actual_inner_scalar_thresholds
    (B : ℝ)(hB : 0≤B)(budget : ℕ) :
    let r:=postDictionaryRate B budget
    let hr:=(postDictionaryRate_budgets hB budget).1
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀U : ℝ,(1/50:ℝ)≤U→
      actualSelectedScalarThreshold budget r hr≤Z^U :=by
  intro r hr
  exact eventually_all_rebased_sources _ (eventually_ge_atTop _)

/-- The actual subset and rebase select one previously fixed metadata
entry. The canonical source, native coarse estimate and physical/OLD
thresholds all belong to that same node. No LOW or energy bound is an
assumption; the source is the original uniform metadata event. -/
theorem actual_inner_low_metadata_at_node
    (dt dd : Finset alpha→ℕ)(ct cd : Finset alpha→Finset (ℕ×ℕ))
    (Kt Cp Kc Cd C0 C1 Kd Kcoarse : Finset alpha→ℝ)
    (Z : ℝ)
    (hsource : ∀U : ℝ,(1/50:ℝ)≤U→∀T : Finset alpha,
      InnerCanonicalSubsetAt hH W hW hWs hbeta hbetaHi eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72
        j hj i S (postDictionaryRate Bnorm (Fintype.card alpha))
        (postDictionaryRate_budgets hB (Fintype.card alpha)).1 T (dt T) (dd T) (ct T) (cd T)
        (Kt T) (Cp T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T) (Z^U) ∧
      NativeLowCoarseSubsetAt T (Fintype.card alpha) S.Cs (Kcoarse T) (Z^U) ∧
      innerPhysicalThreshold hH j (postDictionaryRate Bnorm (Fintype.card alpha))
        (postDictionaryRate_budgets hB (Fintype.card alpha)).1 T≤Z^U ∧
      actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) T.card≤Z^U)
    (C : SourceContext (α:=alpha) M H)(hCW : C.W=W)(hCeta : C.etaSeed=eta)(hCQ : C.Q=Q)
    (hbase : C.globalBase=Z)(N : ReachableNode C j)(hledger : innerLedger j i=N.ledger)
    (hQ0N : internalQ C.Q C.etaSeed≠0)(hQtN : internalQ C.Q C.etaSeed≠⊤) :
    InnerCanonicalNativeSpec hH N hj hQ0N hQtN hbeta S.g S.Cs eps
      (postDictionaryRate Bnorm (Fintype.card alpha)) heps
      (postDictionaryRate_budgets hB (Fintype.card alpha)).1
      (dt N.slots) (ct N.slots) (Kt N.slots) (Cp N.slots) (Kc N.slots)
      (dd N.slots) (cd N.slots) (Cd N.slots) (C0 N.slots) (C1 N.slots) (Kd N.slots) ∧
    NativeLowCoarseSubsetAt N.slots (Fintype.card alpha) S.Cs (Kcoarse N.slots) N.localBase ∧
    innerPhysicalThreshold hH j (postDictionaryRate Bnorm (Fintype.card alpha))
      (postDictionaryRate_budgets hB (Fintype.card alpha)).1 N.slots≤N.localBase ∧
    actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) N.slots.card≤N.localBase :=by
  have canonical:=actual_inner_canonical_spec_from_metadata hH W hW hWs hbeta hbetaHi
    eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72 j hj i S
    (postDictionaryRate Bnorm (Fintype.card alpha))
    (postDictionaryRate_budgets hB (Fintype.card alpha)).1
    dt dd ct cd Kt Cp Kc Cd C0 C1 Kd Z (fun U hU T=>(hsource U hU T).1)
    C hCW hCeta hCQ hbase N hledger hQ0N hQtN
  have hs:=hsource N.unit N.unit_floor N.slots
  rw [←hbase,←N.localBase_eq] at hs
  exact ⟨canonical,hs.2⟩

end
end OAI.SevenEighths.Cycle153InnerLowSchedule
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.actual_inner_low_metadata_at_node
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.eventual_actual_inner_scalar_thresholds
