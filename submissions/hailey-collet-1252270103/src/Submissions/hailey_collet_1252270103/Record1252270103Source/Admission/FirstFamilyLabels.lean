/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Arithmetic labels for the actual modified first source, adapted from Cycle61.
No map into the ordinary unmodified active source is used. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBalancedWindows
import Submissions.hailey_collet_1252270103.Record12518109Raw.FixedParentDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData Cycle61InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

def firstLabel (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) : FirstSourceLabel :=
  ⟨j.1.val.1.val,j.1.val.2.1⟩

def columnIdeal (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) : Ideal O :=
  if reflected then (source s modifier R seed K Z ξ hK key j.1).D
    else (source s modifier R seed K Z ξ hK key j.1).C

def columnPair (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) :=
  let src:=source s modifier R seed K Z ξ hK key j.1
  fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹

def columnCharacter (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) : Character :=
  if reflected then (columnPair s modifier R seed K Z ξ hK key j).right
    else (columnPair s modifier R seed K Z ξ hK key j).left

def dictionaryRay (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) : RayCharacter :=
  let src:=source s modifier R seed K Z ξ hK key j.1
  if reflected then firstPhaseCharacter src.C src.D src.hC
    (fun p=>6-activeExponent src.C src.D p)*j.2.2.2⁻¹
  else firstPhaseCharacter src.C src.D src.hC (activeExponent src.C src.D)*j.2.2.1

theorem column_pair_original (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (source s modifier R seed K Z ξ hK key)) :
    columnPair s modifier R seed K Z ξ hK key (firstSectorColumn _ q)=
      QRH.Record1252270103Source.High.CoupledFirst.originalFirstPair s modifier R seed K Z ξ hK
        (QRH.Record1252270103Source.High.CoupledFirst.geometryOriginalSector s modifier R seed K Z ξ hK key q) := rfl

theorem column_supported (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) :
    Supported (columnIdeal reflected s modifier R seed K Z ξ hK key j) := by
  cases reflected
  · exact (source s modifier R seed K Z ξ hK key j.1).hC
  · exact (source s modifier R seed K Z ξ hK key j.1).hD

theorem column_modulus (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) :
    let src:=source s modifier R seed K Z ξ hK key j.1
    (columnCharacter reflected s modifier R seed K Z ξ hK key j).modulus=
      s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*
          activeConductor src.C src.D} := by
  cases reflected
  · exact (columnPair s modifier R seed K Z ξ hK key j).left_modulus
  · exact (columnPair s modifier R seed K Z ξ hK key j).right_modulus

end
end QRH.Record1252270103Source.Admission.FirstFamily
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.column_pair_original
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.column_supported
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.column_modulus
