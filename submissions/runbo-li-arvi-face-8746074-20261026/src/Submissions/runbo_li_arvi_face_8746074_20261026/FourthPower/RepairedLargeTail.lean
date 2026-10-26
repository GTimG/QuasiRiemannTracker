/- Copyright (c) 2026 Sil. Apache-2.0.
Actual large nonexceptional block for a GENERIC root Source. The ordinary
reference and Source.L may move. Canonical/geometric inputs are structural;
the checked analytic block supplier and actual root admission are invoked
inside, not supplied as energy hypotheses.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedBlockUniformity
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRootParameters
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRawRetained
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshRootAdmission

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedLargeTail
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ConcreteTraceCRT RayFourExpansion ActualEisensteinCubic
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondBlockAggregate MixedFirstExceptionalWindow OuterFreshAllocatedWindow
open CenteredMomentSecondRetainedAggregate
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar CenteredMomentUncenteredTerminal
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiveNormalization
open MixedFirstLiveSource MixedFirstActualNonexceptional MixedFirstSourceGeometry
open MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstCutoffs MixedFirstExceptionalNormalization
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierSource
open OuterFreshSource OuterFreshSelectedWindow OuterFreshSelection OuterFreshSelected
open OuterFreshRootAdmission OuterFreshCutoffAllowance OuterFreshNonexceptionalFamily
open OuterFreshWindowPair OuterFreshConsumer OuterFreshNonexceptionalBlock OuterFreshSelectedKernel
open OuterFreshAllocationMass RepairedBlockUniformity RepairedRootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ:=Classical.decEq _

variable {α : Type u} [Fintype α]
/-- Physical tail with an ABSTRACT first source. It is a named conclusion,
not an assumed energy field. Root allocation construction is outside it. -/
def Result (N : ℕ) (ε : ℝ) (hε : 0 < ε) (Kslot : ℝ)
    (degree : ℕ) (control : Finset (ℕ × ℕ)) (Cbound Z t₀ V : ℝ) (Q : Id)
    (first : Source α (1/4) (9/4)) (cover₁ : OriginalEnclosure first)
    (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh ε)
    (η : Character) (C₁ D₁ : Id) (E₁ : Finset (CommonIndex C₁ D₁)) (Kroot Vroot : ℝ) : Prop :=
    ∀τ:Character,
      τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P:CommonIndex C₁ D₁=>P.val) E₁*activeConductor C₁ D₁} →
    ∀n₁:ℤ,Retained (frequencyRadius (firstCutoff C₁ D₁ E₁ Kroot Vroot)
      Z (cutoffLoss N ε)) n₁ →
    ∀u:Id,∀L:Finset α,widthFloor ε<liveWidth L w →
    let J:=chosenSlots L w (widthFloor ε) (mesh ε)
      (mesh_spec ε hε).1.le hw hwm
    let q : Data α := supplierData first (by norm_num) u L J
    ∀x:Frozen q,MixedSupplierFourthRow.frozenWeight q x≠0 →
    ∀seed:Id,Squarefree seed → u=frozenProduct q x*seed →
    ∀p₂:FixedLabel (fixedPool q x (residualSource first (by norm_num) cover₁ u L J x) seed),
    ∀(ξ χ₀:RayCharacter)(U:Finset (CommonIndex p₂.val.1 p₂.val.2))(n₂:Fin 4 → ℤ)(tp:ℝ),
    let Kchild : ℝ := nominalChildScale C₁ D₁ E₁ Kroot Vroot Z (cutoffLoss N ε) n₁
    let ra : Source (RestIndex q) (1/4) (9/4) := residualSource first (by norm_num) cover₁ u L J x
    let r : Source (RestIndex q) (1/4) (9/4) := unavoidedResidual first (by norm_num) cover₁ u L J x
    let Rfreq : ℝ := frequencyRadius (secondSourceCutoff (ι:=RestIndex q) (a:=1/4) (b:=9/4) ra Kchild) Z (cutoffLoss N ε)
    let Rdecl : ℝ := declaredWidth q η Kroot Z (deficit C₁ D₁ E₁ Kroot Vroot Z n₁)
      (Real.logb Z (C₁.absNorm:ℝ)) (cutoffLoss N ε) p₂.val.1 p₂.val.2 U
    let H : ℂ := heightCoeff τ tp p₂.val.1*star (heightCoeff τ tp p₂.val.2)
    let Budget : ℝ := Z^(artificialLoss N ε)*
      Real.sqrt (((p₂.val.1.absNorm:ℝ)^(commonPower N ε)*(rootFactor r/(p₂.val.1.absNorm:ℝ)))*
        ((p₂.val.2.absNorm:ℝ)^(commonPower N ε)*(rootFactor r/(p₂.val.2.absNorm:ℝ))))*
      angleEnvelope r 1 Kslot N degree control t₀ tp V Z Rdecl (windowLoss ε)
    Z^(stepN N ε)*‖normalization (r.X₁*r.X₂) r.P‖^2*
      ‖H*physicalAverage q x ra seed τ ξ χ₀ Q p₂.val.1 p₂.val.2
        (commonLabels_supported _ _ _ p₂.property).1 (commonLabels_supported _ _ _ p₂.property).2
        U tp Rfreq ballProfile Kchild n₂‖≤
      Cbound*(outerScalar p₂.val.1 p₂.val.2 Kchild n₂*normalizer p₂.val.1 p₂.val.2 U)*(‖H‖*Budget)

end
end Candidate.FourthPower.RepairedLargeTail
