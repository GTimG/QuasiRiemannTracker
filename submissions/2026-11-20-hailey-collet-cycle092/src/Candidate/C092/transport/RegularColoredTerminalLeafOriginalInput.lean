/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafMediumUniform
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
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOriginalInput_0c13ccc68d1ccfc5_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Literal live original-row data. The two norm dictionaries are the native
anchored coefficient identities on the same selected slots and sparse rows. -/
structure TerminalOriginalInput (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (n y mesh U V : ℝ) where
  T : Finset Slot
  rows : Finset FreeRow
  theta : Slot→RayQuotient.Characters M A.Hr
  thetaLong : Slot→RayQuotient.Characters M A.Hr
  thetaShort : Slot→RayQuotient.Characters M A.Hr
  w : Slot→ℝ
  sigma : Slot→ℝ
  v : Slot→ℝ
  vLong : Slot→ℝ
  vShort : Slot→ℝ
  tOld : ℝ
  tLong : ℝ
  tShort : ℝ
  height : ℝ
  height_nonneg : 0 ≤ height
  old_height : |tOld| ≤ height
  pitch : ∀j,|v j| ≤ height
  pitchLong : ∀j,|vLong j| ≤ height
  pitchShort : ∀j,|vShort j| ≤ height
  width_nonneg : ∀j,0 ≤ w j
  width_mesh : ∀j,w j ≤ mesh
  width_sum : (∑j∈T,w j) ≤ sourceWidth n y-(u:ℝ)
  sigma_eq : ∀j,sigma j=33/50
  X : ℝ
  Y : ℝ
  long_positive : 0 < X
  short_positive : 0 < Y
  long_cap : X ≤ U^n
  short_cap : Y ≤ U^y
  old_keep : ∀z∈rows,initialKeep A.old A.Qold z.val
  long_keep : ∀z∈rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) z.val
  short_keep : ∀z∈rows,initialKeep A.ηShort (internalQ A.QShort A.baseShort) z.val
  row_norm : ∀z∈rows,rowNorm z ≤ U^V
  long_presentation : ∀z∈rows,∀j∈T,
    ‖originalMark M A.Hr A.hHr A.old A.base theta A.W U w sigma v tOld j z‖=
      ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 z.val
        (originalPools M A.Hr 2 U w j)
        (originalCoefficients M A.Hr A.hHr A.baseLong thetaLong A.W U w sigma vLong j)
        tLong (U^(w j))‖
  short_presentation : ∀z∈rows,∀j∈T,
    ‖originalMark M A.Hr A.hHr A.old A.base theta A.W U w sigma v tOld j z‖=
      ‖normalizedSlot A.ηShort (fixedBadMask*idealGenerator 1) 1 z.val
        (originalPools M A.Hr 2 U w j)
        (originalCoefficients M A.Hr A.hHr A.baseShort thetaShort A.W U w sigma vShort j)
        tShort (U^(w j))‖

namespace TerminalOriginalInput
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M]
variable {A : Arithmetic M} {n y mesh U V : ℝ}
variable (F : TerminalOriginalInput Slot M A n y mesh U V)
def mark : Slot→FreeRow→ℂ := originalMark M A.Hr A.hHr A.old A.base F.theta A.W U F.w F.sigma F.v F.tOld
def response (buffer Cslot : ℝ) (z : FreeRow) : ℝ :=
  LowActual.response U (Cslot*U^buffer) (fun j:F.T=>F.w j.val) (fun j=>‖F.mark j.val z‖^2)
def mediumRows (buffer Cslot threshold : ℝ) : Finset FreeRow :=
  F.rows.filter (fun z=>threshold<F.response buffer Cslot z ∧ F.response buffer Cslot z≤(responseUpper:ℝ))
def energy (rows : Finset FreeRow) (p : Profiles (1/4) (9/4)) : ℝ :=
  finiteEnergyOn F.T rows A.ηLong A.ηShort (p.profile 0) (p.profile 1) F.tLong F.tShort F.X F.Y F.mark

theorem descriptor_short (z : FreeRow) (hz : z∈F.rows) (j : F.T) :
    ‖F.mark j.val z‖=‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U
      (fun j:F.T=>F.thetaShort j.val) (fun j:F.T=>F.w j.val) (fun j:F.T=>F.vShort j.val) F.tShort z j‖ := by
  rw [descriptor_short_anchor M A.Hr A.hHr A.ηShort A.baseShort A.W U
    (fun j:F.T=>F.thetaShort j.val) (fun j:F.T=>F.w j.val) (fun j:F.T=>F.sigma j.val)
    (fun j:F.T=>F.vShort j.val) F.tShort z j (F.sigma_eq j.val)]
  exact F.short_presentation z hz j.val j.property

theorem descriptor_long (z : FreeRow) (hz : z∈F.rows) (j : F.T) :
    ‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U
      (fun j:F.T=>F.thetaShort j.val) (fun j:F.T=>F.w j.val) (fun j:F.T=>F.vShort j.val) F.tShort z j‖=
    ‖descriptor M A.Hr A.hHr A.ηLong A.baseLong A.W U
      (fun j:F.T=>F.thetaLong j.val) (fun j:F.T=>F.w j.val) (fun j:F.T=>F.vLong j.val) F.tLong z j‖ := by
  rw [←F.descriptor_short z hz j]
  rw [descriptor_short_anchor M A.Hr A.hHr A.ηLong A.baseLong A.W U
    (fun j:F.T=>F.thetaLong j.val) (fun j:F.T=>F.w j.val) (fun j:F.T=>F.sigma j.val)
    (fun j:F.T=>F.vLong j.val) F.tLong z j (F.sigma_eq j.val)]
  exact F.long_presentation z hz j.val j.property

theorem response_measured (buffer Cslot : ℝ) (z : FreeRow) (hz : z∈F.rows) :
    F.response buffer Cslot z=measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer)
      (fun j:F.T=>F.thetaShort j.val) (fun j:F.T=>F.w j.val) (fun j:F.T=>F.vShort j.val) F.tShort z :=
  response_norm_congr U (Cslot*U^buffer) (fun j:F.T=>F.w j.val) (fun j=>F.mark j.val z) _
    (F.descriptor_short z hz)
end TerminalOriginalInput
#print axioms TerminalOriginalInput.response_measured
end
end QRH.Cycle092.RegularColoredForward
