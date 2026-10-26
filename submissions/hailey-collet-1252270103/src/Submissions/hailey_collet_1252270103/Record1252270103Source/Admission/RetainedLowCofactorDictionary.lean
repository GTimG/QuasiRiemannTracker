/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained fixed-L dictionary, including all forced and Newton punctures. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyNewtonPacket
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedForcedGeometryCaps
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentNaturalRowSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass Record12518109Raw
open FirstFamily
local notation "O"=>HeckeFamily.O
local notation "source"=>QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

lemma coprime_forced_iff (I L C : Ideal O) (hLC : L∣C) (hCL : C∣L^2) :
    IsCoprime I C ↔ IsCoprime I L := by
  refine ⟨fun h=>h.of_isCoprime_of_dvd_right hLC,fun h=>?_⟩
  exact (h.pow_right).of_isCoprime_of_dvd_right hCL

lemma excluded_forced_seed (χ : Character) (P L C J : Ideal O)
    (hP : P≠0) (hL : L≠0) (hC : C≠0) (hJ : J≠0)
    (hLC : L∣C) (hCL : C∣L^2) (I : Ideal O) :
    idealCoeff (excluded χ (P*(C*J))) I=idealCoeff (excluded χ (P*(L*J))) I := by
  rw [excluded_ideal _ _ (mul_ne_zero hP (mul_ne_zero hC hJ)),
    excluded_ideal _ _ (mul_ne_zero hP (mul_ne_zero hL hJ))]
  simp only [IsCoprime.mul_right_iff,coprime_forced_iff I L C hLC hCL]

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (reflected second : Bool) (s : Input α) (modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
    (datum : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (row : secondLiveRows (fun l=>(datum l).block))
    (hfirst : first row.val.1=firstLabel s modifier R seed K Z ξ hK bin column)
local notation "key"=>rawKey reflected s modifier R seed K Z ξ hK bin column datum first row hfirst second
local notation "dd"=>datum row.val.1
local notation "zz"=>(if second then -row.val.2.2.2.val else row.val.2.2.2.val)

lemma actual_row_ne : zz≠0 := by
  cases second
  · exact (dd).rows_ne _ row.val.2.2.2.property
  · exact neg_ne_zero.mpr ((dd).rows_ne _ row.val.2.2.2.property)

lemma actual_key_support :
    (Supported (key).val.1.1.1 ∧ (key).val.1.1.2≠0 ∧ Supported (key).val.2.1.1 ∧ (key).val.2.1.2≠0) ∧
    (CompletedGauss.primeSupport (key).val.1.1.1=CompletedGauss.primeSupport (key).val.1.1.2 ∧
      CompletedGauss.primeSupport (key).val.2.1.1=CompletedGauss.primeSupport (key).val.2.1.2) := by
  have hk : (key).val.1=firstLabel s modifier R seed K Z ξ hK bin column := by
    cases second <;> exact hfirst
  have hs:=FirstFamily.label_supported s modifier R seed K Z ξ hK bin column
  have hp : (key).val.2.1=((dd).C,(dd).D) := by cases second <;> rfl
  rw [hk,hp]
  exact ⟨⟨hs.1,hs.2.1.1,(dd).hC,(dd).hD.1⟩,hs.2.2,(dd).sameSupport⟩


end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.coprime_forced_iff
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.excluded_forced_seed
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.actual_row_ne
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.actual_key_support
