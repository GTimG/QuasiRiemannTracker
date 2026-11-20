/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOuterActual
import Candidate.C092.transport.RegularColoredTerminalLeafMediumUniform
import Candidate.C092.transport.P2InverseTicketDispatchActual
import Candidate.C092.transport.RegularColoredTerminalLeafAggregate
import Candidate.C092.transport.StrongPairRegularTerminalReserve
set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularP2BranchCollection_9555e716cdcaa2c4_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

/-- One constant for the original row partition; it precedes the profiles
and heights. Its strictly positive unit term covers a vanishing profile. -/
def collectedConstant (L : LateBundle P G m0 gap kernel) (I:ℕ) (Cslot CLo K:ℝ) :=
  L.normalizationConstant^4*
    (QuadraticInitialBound.diagonalControl radialMajorant*(P.small.C+CLo)+
      K*terminalMediumEnvelope L I Cslot+1)

theorem collect_actual_branches (L : LateBundle P G m0 gap kernel) {U V Cslot CLo mesh K:ℝ} {I:ℕ}
    (hAt:AtAll P G L.Bshort m0 gap L.sources I Cslot CLo U) (hU:1<U)
    (F:TerminalOriginalInput Slot M A n y mesh U V) (p:Profiles (1/4) (9/4))
    (hV:0 ≤ V) (hVmax:V ≤ Vmax) (hy:0 ≤ y) (hn:0 ≤ n)
    (hsm:mesh ≤ smallMesh) (hlm:mesh ≤ lowMesh) (hOld:|F.tOld|+F.height ≤ U^(1/2:ℝ))
    (he:e ≤ (responseUpper:ℝ)) (hCslot:1 ≤ Cslot) (hLo:0 ≤ CLo) (hK:0 ≤ K)
    (medium : (98/100:ℝ)<V → F.energy (F.mediumRows buffer Cslot e) p  ≤ 
      K*L.normalizationConstant^4*(p.control L.controlsBound)^2*
        terminalMediumEnvelope L I Cslot*U^(StrongPair.terminalFramePrice V)) :
    F.energy F.rows p  ≤  collectedConstant L I Cslot CLo K*(p.control L.controlsBound)^2*
      (1+|F.tLong|+|F.tShort|+F.height)^P.degreeBound*U^(StrongPair.terminalFramePrice V) := by
  let A:=L.normalizationConstant^4*(p.control L.controlsBound)^2
  let Ht:=1+|F.tLong|+|F.tShort|+F.height
  let Z:=U^(StrongPair.terminalFramePrice V)
  let price:=V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)
  let diag:=QuadraticInitialBound.diagonalControl radialMajorant
  let env:=terminalMediumEnvelope L I Cslot
  have hd:0 ≤ diag:=QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have henv:0 ≤ env:=(terminal_medium_envelope_bounds L I (show 0 ≤ Cslot by linarith)).1.le
  have hsmall:0 ≤ P.small.C:=P.small.positive.le
  have hA:0 ≤ A:=mul_nonneg (by positivity) (sq_nonneg _)
  have hH:1 ≤ Ht:=by dsimp [Ht];linarith [F.height_nonneg,abs_nonneg F.tLong,abs_nonneg F.tShort]
  have hH0:=zero_le_one.trans hH
  have hHd:=one_le_pow₀ (n:=P.degreeBound) hH
  have hZ:0 ≤ Z:=Real.rpow_nonneg (zero_lt_one.trans hU).le _
  have hp:U^price ≤ Z:=by
    apply Real.rpow_le_rpow_of_exponent_le hU.le
    dsimp [price,StrongPair.terminalFramePrice,StrongPair.terminalReserve]
    norm_num [rho];linarith
  have payments:=L.profile_payments p
  have degrees:=P.degree_bounds
  have upper (c pc:ℝ) (dd:ℕ) (hc:0 ≤ c) (hpc:pc^2 ≤ A) (hdd:dd ≤ P.degreeBound) :
      c*diag*pc^2*Ht^dd*U^price  ≤  (c*diag)*(A*Ht^P.degreeBound*Z) := by
    have h:=mul_le_mul (mul_le_mul hpc (pow_le_pow_right₀ hH hdd) (pow_nonneg hH0 _) hA) hp
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (mul_nonneg hA (pow_nonneg hH0 _))
    convert mul_le_mul_of_nonneg_left h (mul_nonneg hc hd) using 1 <;> ring
  have scale:0 ≤ A*Ht^P.degreeBound*Z:=mul_nonneg (mul_nonneg hA (pow_nonneg hH0 _)) hZ
  let total:=diag*(P.small.C+CLo)+K*env+1
  have htotal : F.energy F.rows p  ≤  total*(A*Ht^P.degreeBound*Z) := by
    by_cases hs: V ≤ 98/100
    · have h:=terminal_actual_small_input_at L hAt F hV hs hy hn hsm hOld p
      have hu:=upper P.small.C _ _ hsmall payments.1 degrees.1
      apply (h.trans hu).trans
      apply mul_le_mul_of_nonneg_right _ scale
      dsimp [total];nlinarith only [mul_nonneg hd hLo,mul_nonneg hK henv]
    · let lo := F.rows.filter (fun z=>F.response buffer Cslot z ≤ e)
      let hi := F.rows.filter (fun z=>(responseUpper:ℝ)<F.response buffer Cslot z)
      have h:=terminal_actual_low_high_input_at L hAt F (le_of_not_ge hs) hVmax hy hn hlm p
      have hu:=upper CLo _ _ hLo payments.2.1 degrees.2.1
      have hm:=medium (lt_of_not_ge hs)
      have hmp : F.energy (F.mediumRows buffer Cslot e) p  ≤  (K*env)*(A*Ht^P.degreeBound*Z) := by
        apply hm.trans
        have ha:=mul_le_mul_of_nonneg_right hHd (mul_nonneg (mul_nonneg (mul_nonneg hK henv) hA) hZ)
        convert ha using 1 <;> dsimp only [A,env,Z] <;> ring
      have heq : F.energy F.rows p = F.energy lo p + F.energy hi p + F.energy (F.mediumRows buffer Cslot e) p :=
        terminal_energy_response_partition _ _ _ _ _ _ _ _ _ _ _ (F.response buffer Cslot) he
      rw [heq]
      apply (add_le_add (h.trans hu) hmp).trans
      rw [←add_mul]
      apply mul_le_mul_of_nonneg_right _ scale
      dsimp [total];nlinarith only [mul_nonneg hd hsmall]
  apply htotal.trans_eq
  dsimp only [total,A,Ht,Z,diag,env,collectedConstant]
  ring

#print axioms collect_actual_branches
end
end QRH.Cycle092.RegularColoredForward
