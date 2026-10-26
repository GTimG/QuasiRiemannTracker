/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Supported first-label identities use Gao PR63 / OpenAI/math source interfaces,
with their original Apache-2.0 attribution retained in the imported modules. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.ActualFloors
import Submissions.hailey_collet_1252270103.Record12518109Source.GlobalPayments
import Submissions.hailey_collet_1252270103.Record12518109Natural.HighAllocation
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CompletedGauss Record12518109Natural
open Cycle61Moment Cycle61HighGeometry Cycle61InitialMass CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstSourceReduction
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

theorem actualFirstVector_flip (reflected : Bool) (C D : Ideal O) (Z : ℝ) :
    firstFlip (actualFirstVector reflected C D Z)=actualFirstVector (!reflected) C D Z := by
  cases reflected <;> funext k <;> fin_cases k <;>
    simp [firstFlip,actualFirstVector,firstJoin,Valuation.actualVector]

theorem actualFirstVector_fields (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) :
    let v:=actualFirstVector reflected l.1.1 l.1.2 Z
    v 0=labelC reflected l Z ∧ v 1=labelD reflected l Z ∧ v 2=labelP l Z ∧
      v 3=labelR l Z ∧
      v 4=Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ) ∧
      v 5=Real.logb Z ((Ideal.span {firstSourceNumerator reflected l}).absNorm:ℝ) ∧
      v 6=Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ) ∧
      v 7=Real.logb Z ((cancelledRadical reflected l.1.1 l.1.2).absNorm:ℝ) := by
  cases reflected <;>
    simp [actualFirstVector,firstJoin,Valuation.actualVector,labelC,labelD,labelP,labelR,
      firstSourceNumerator]

theorem actualFirstVector_surplus (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) :
    globalSigma (actualFirstVector reflected l.1.1 l.1.2 Z)=labelSurplus reflected l Z := by
  cases reflected <;>
    simp [globalSigma,globalB_false,globalB_true,firstLinear,actualFirstVector,firstJoin,
      Valuation.actualVector,labelSurplus,labelC,labelD,labelP,labelR] <;> ring

def FirstPairPayments (c : Cell) (v : Fin 8→ℝ) : Prop :=
  0≤globalSigma v ∧ 0≤globalLocalization v ∧
    (v 0≤v 1 → globalLow c (17/50) v+globalLow c (17/25) (firstFlip v)≤0) ∧
    (∀ν : ℝ,ν ∈ Set.Icc c.q (3/4) →
      d ν*globalLow c omega v+globalHighScaled ν (firstFlip v)≤0) ∧
    (∀l r : ℝ,l ∈ Set.Icc c.q (3/4) → r ∈ Set.Icc c.q (3/4) →
      globalHigh l v+globalHigh r (firstFlip v)≤-gamma c*(v 0+v 1)) ∧
    (∀ν : ℝ,ν ∈ Set.Icc c.q (3/4) →
      (∀p : Bool,0≤globalFloor c p ν v) ∧ 0≤globalComplement c ν v)

theorem actual_first_pair_payments (k : Fin 15) (reflected : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C=primeSupport D)
    (Z : ℝ) (hZ : 1<Z) :
    FirstPairPayments (rawCells k) (actualFirstVector reflected C D Z) := by
  obtain ⟨hordered,hsigma,hloc,hmixed,hpaired⟩ := actual_first_cones k reflected C D hC hD heq Z hZ
  refine ⟨hsigma,hloc,?_,?_,?_,?_⟩
  · intro ho
    rw [ordered_pair_identity _ _ ho]
    exact hordered
  · intro ν hν
    exact mixed_pair_payment _ _ _ (hmixed ν hν)
  · intro l r hl hr
    exact paired_high_payment _ _ _ _ (hpaired l r hl hr)
  · intro ν hν
    exact actual_first_floors k reflected C D hC hD heq Z hZ hν

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- Every literal first-column geometry label satisfies the complete common
payment contract. No freely supplied scalar valuation cone remains. -/
theorem geometry_first_pair_payments (k : Fin 15)
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (reflected : Bool) (hZ : 1<Z) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    FirstPairPayments (rawCells k) (actualFirstVector reflected l.1.1 l.1.2 Z) ∧
      globalSigma (actualFirstVector reflected l.1.1 l.1.2 Z)=
        QRH.Record12518109Assembly.surplus (geometryExponents s R seed K Z xi j.1.val) := by
  intro l
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z xi hK bin j.1).sameSupport
  refine ⟨actual_first_pair_payments k reflected l.1.1 l.1.2 hC hD heq Z hZ,?_⟩
  exact (actualFirstVector_surplus reflected l Z).trans
    (geometry_label_surplus_eq s R seed K Z xi hK bin j reflected)

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.actualFirstVector_fields
#print axioms QRH.Record12518109Source.actual_first_pair_payments
#print axioms QRH.Record12518109Source.geometry_first_pair_payments
