/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalInput
import Candidate.C092.transport.RegularP2AllHeights
import Candidate.C092.transport.RegularColoredTerminalLeafStateInput
import Candidate.C092.transport.P2StageScalarsLate
import Candidate.C092.transport.RegularColoredTerminalLeafOccupied
import Candidate.C092.transport.RegularColoredTerminalLeafLengths
import Candidate.C092.transport.RegularColoredTerminalLeafHomogeneous
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafBoundedNative_bcce5be2f173bb11_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def TerminalBoundedOriginalAt (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (n y mesh U kappa : ℝ)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀V : ℝ,0 ≤ V → V ≤ 2 → ∀F : TerminalOriginalInput Slot M A n y mesh U V,
    1 ≤ F.Y → 1+|F.tLong|+|F.tShort|+F.height ≤ U^kappa →
    ∀p : Profiles (1/4) (9/4),F.energy F.rows p ≤
      C*(p.control controls)^2*(1+|F.tLong|+|F.tShort|+F.height)^degree*U^(terminalFramePrice V)

/-- The two independent anchored arithmetic tuples retain the original
ordinary character and mark prefix, with the genuine internal keep ideals. -/
def terminal_pair_arithmetic
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M ≤ Hr)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (hΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (old base omega1 omega2 : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ10 : internalQ Q (base.product omega1)≠0) (hQ1t : internalQ Q (base.product omega1)≠⊤)
    (hQ172 : internalQ Q (base.product omega1) ≤ Ideal.span {(72:O)})
    (hQ20 : internalQ Q (base.product omega2)≠0) (hQ2t : internalQ Q (base.product omega2)≠⊤)
    (hQ272 : internalQ Q (base.product omega2) ≤ Ideal.span {(72:O)}) : Arithmetic M := {
  Hr:=Hr,hHr:=hHr,W:=W,hW:=hW,hWs:=hWs,bΦ:=bΦ,hbΦ:=hbΦ,hΦ:=hΦ,
  old:=old,base:=base,Qold:=internalQ Q base,hQoldM:=inf_le_left.trans hQM,hQoldBase:=inf_le_right,
  ηLong:=old.product omega1,ηShort:=old.product omega2,baseLong:=base.product omega1,baseShort:=base.product omega2,
  QLong:=Q,QShort:=Q,hQLM:=hQM,hQL0:=hQ10,hQLt:=hQ1t,hQL72:=hQ172,
  hQSM:=hQM,hQS0:=hQ20,hQSt:=hQ2t,hQS72:=hQ272 }

theorem terminal_bounded_ordered_of_original
    {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M ≤ Hr)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (hΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (old base omega1 omega2 : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ10 : internalQ Q (base.product omega1)≠0) (hQ1t : internalQ Q (base.product omega1)≠⊤)
    (hQ172 : internalQ Q (base.product omega1) ≤ Ideal.span {(72:O)})
    (hQ20 : internalQ Q (base.product omega2)≠0) (hQ2t : internalQ Q (base.product omega2)≠⊤)
    (hQ272 : internalQ Q (base.product omega2) ≤ Ideal.span {(72:O)})
    {n y mesh U kappa C : ℝ} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (source : TerminalBoundedOriginalAt Slot M
      (terminal_pair_arithmetic M Hr hHr W hW hWs bΦ hbΦ hΦ old base omega1 omega2 Q hQM
        hQ10 hQ1t hQ172 hQ20 hQ2t hQ272) n y mesh U kappa degree controls C) :
    QRH.Cycle092.RegularFramePhysicalReturn.BoundedOrderedP2At Slot M Hr hHr W n y mesh U
      old base omega1 omega2 Q degree controls C kappa := by
  intro V hV hV2 T theta w sigma freq tOld t1 t2 height hw hwm hSigma hh ht hf hf1 hf2 hwidth
    p X Y hX hY hXcap hYcap hYone hheight rows hOld hLong hShort hRow hNormLong hNormShort
  let A:=terminal_pair_arithmetic M Hr hHr W hW hWs bΦ hbΦ hΦ old base omega1 omega2 Q hQM
    hQ10 hQ1t hQ172 hQ20 hQ2t hQ272
  let F : TerminalOriginalInput Slot M A n y mesh U V := {
    T:=T,rows:=rows,theta:=theta,thetaLong:=theta,thetaShort:=theta,w:=w,sigma:=sigma,
    v:=freq,vLong:=fun i=>tOld+freq i-t1,vShort:=fun i=>tOld+freq i-t2,
    tOld:=tOld,tLong:=t1,tShort:=t2,height:=height,height_nonneg:=hh,old_height:=ht,
    pitch:=hf,pitchLong:=hf1,pitchShort:=hf2,width_nonneg:=hw,width_mesh:=hwm,width_sum:=hwidth,sigma_eq:=hSigma,
    X:=X,Y:=Y,long_positive:=hX,short_positive:=hY,long_cap:=hXcap,short_cap:=hYcap,
    old_keep:=hOld,long_keep:=hLong,short_keep:=hShort,row_norm:=hRow,
    long_presentation:=hNormLong,short_presentation:=hNormShort }
  exact source V hV hV2 F hYone hheight p

#print axioms terminal_bounded_ordered_of_original
end
end QRH.Cycle092.RegularColoredForward
