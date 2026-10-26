/- The prechosen original-subset canonical source at the actual inner node.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.InnerLowCanonicalMetadata
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalInvoke

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153InnerLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle153RegionalLow Cycle153SourceUniform Cycle153SourceSchedule
open Cycle153TerminalSchedule Cycle153Reachable Cycle153ActualColumn
attribute [local irreducible] NativeCanonicalPaidColumnsAt
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
variable (eps tau Bnorm : ℝ)(heps : 0<eps)(eta : Character)(Q : Ideal O)
variable (hQM : Q≤M)(hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(j : Fin 4)(hj : j.val<3)
variable (i : InnerGridIndex j)
variable (S : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
  eps tau Bnorm heps eta Q hQM hQ72 j i)

/-- Select the actual original subset and its actual rebase unit from a
uniform pre-Z source event. The native driver is retained; only the literal
Fourier cardinal is the actual subset cardinal. No source energy is assumed. -/
theorem actual_inner_canonical_spec_from_metadata
    (epsShell : ℝ)(hShell : 0<epsShell)
    (dt dd : Finset alpha→ℕ)(ct cd : Finset alpha→Finset (ℕ×ℕ))
    (Kt Cp Kc Cd C0 C1 Kd : Finset alpha→ℝ)
    (Z : ℝ)
    (hsource : ∀U : ℝ,(1/50:ℝ)≤U→∀T : Finset alpha,
      InnerCanonicalSubsetAt hH W hW hWs hbeta hbetaHi eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72
        j hj i S epsShell hShell T (dt T) (dd T) (ct T) (cd T)
        (Kt T) (Cp T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T) (Z^U))
    (C : SourceContext (α:=alpha) M H)(hCW : C.W=W)(hCeta : C.etaSeed=eta)(hCQ : C.Q=Q)
    (hbase : C.globalBase=Z)(N : ReachableNode C j)(hledger : innerLedger j i=N.ledger)
    (hQ0N : internalQ C.Q C.etaSeed≠0)(hQtN : internalQ C.Q C.etaSeed≠⊤) :
    InnerCanonicalNativeSpec hH N hj hQ0N hQtN hbeta S.g S.Cs eps epsShell heps hShell
      (dt N.slots) (ct N.slots) (Kt N.slots) (Cp N.slots) (Kc N.slots)
      (dd N.slots) (cd N.slots) (Cd N.slots) (C0 N.slots) (C1 N.slots) (Kd N.slots) :=by
  have hs:=hsource N.unit N.unit_floor N.slots
  rw [←hbase,←N.localBase_eq] at hs
  let P : Cycle63.AffineLedger→Prop:=fun L=>
    letI : Cycle63.AffineLedger:=L
    NativeCanonicalPaidColumnsAt (alpha:=alpha) (Current:=N.slots) hH W hWs hW eta Q hQM hQ0 hQt hQ72
      1 (oldLoss eps) (oldLoss eps) (by norm_num) (oldLoss_pos heps) (oldLoss_pos heps)
      hbeta (nextInner j hj) (originalSubsetEmbedding N.slots)
      1 31 S.g.τ S.g.δ S.g.e S.g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) S.g.τ_pos S.g.δ_pos
      S.g.e_pos S.g.e_cap S.g.κ_pos (by norm_num) (by simpa only [mul_one] using S.g.budget)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
      (dt N.slots) (ct N.slots) (Kt N.slots) (Cp N.slots) (Kc N.slots) N.localBase N.slots.card S.Cs
      (dd N.slots) (cd N.slots) (Cd N.slots) (C0 N.slots) (C1 N.slots) (Kd N.slots) eps
  have hP : P (innerLedger j i):=hs
  have hN : P N.ledger:=Eq.mp (congrArg P hledger) hP
  simpa only [P,InnerCanonicalNativeSpec,←hCW,←hCeta,←hCQ,Fintype.card_coe] using hN


end
end OAI.SevenEighths.Cycle153InnerLowSchedule
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.actual_inner_canonical_spec_from_metadata
