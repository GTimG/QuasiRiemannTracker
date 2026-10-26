/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified first geometry payment, adapted from pinned Cycle61. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalGeometryBins
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryPayment
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.Normalization

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
open OAI OAI.SevenEighths Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance modifiedGeometryPaymentSumDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma actual_geometry_fiber_difference (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1<Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (key : ℤ×(Fin 5→ℤ))
    (q r : CommonGeometryFiber s modifier R seed K Z ξ key) (i : Fin 5) :
    geometryExponents s modifier R seed K Z ξ q.val i-geometryExponents s modifier R seed K Z ξ r.val i≤
      Real.logb Z 2 := by
  have hq := actual_geometry_fiber_range s modifier R seed K Z ξ B hZ hs hz₁ hz₂ hsource key q i
  have hr := actual_geometry_fiber_range s modifier R seed K Z ξ B hZ hs hz₁ hz₂ hsource key r i
  nlinarith

omit [DecidableEq ι] in
/-- The single-label balance is used only after the five arithmetic
coordinates have been frozen to one common bin. -/
lemma actual_geometry_balance (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ M A : ℝ)
    (hZ : 1<Z) (q : SourceCoordinate s modifier R seed K Z ξ) :
    outsideExponent M A (geometryExponents s modifier R seed K Z ξ q)+
      (leftExponent A (geometryExponents s modifier R seed K Z ξ q)+
       rightExponent A (geometryExponents s modifier R seed K Z ξ q))/2≤M := by
  have hsup : CanonicalQuadraticSieve.Supported q.1.val.1 ∧
      CanonicalQuadraticSieve.Supported q.1.val.2 := CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) q.1.val.1 q.1.val.2 q.1.property
  have hc := actual_labels_commonPart s modifier R seed K Z ξ q
  have hh := Cycle61.Physical.actual_joint_side_exponent q.1.val.1 q.1.val.2 hsup.1 hsup.2
    Z M A (geometryExponents s modifier R seed K Z ξ q 4) hZ
  dsimp only at hh
  rw [hc.1,hc.2] at hh
  change outsideExponent M A (geometryExponents s modifier R seed K Z ξ q)+
    (leftExponent A (geometryExponents s modifier R seed K Z ξ q)+
      rightExponent A (geometryExponents s modifier R seed K Z ξ q))/2≤M at hh
  exact hh

omit [DecidableEq ι] in
/-- Uniform cross-label payment. The left and right labels may differ;
no sum of per-label Cauchy estimates is substituted for joint Cauchy. -/
theorem actual_geometry_cross_payment (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q r : CommonGeometryFiber s modifier R seed K Z ξ key) :
    Z^(outsideExponent M A (geometryExponents s modifier R seed K Z ξ q.val))*
      Real.sqrt (Z^(leftExponent A (geometryExponents s modifier R seed K Z ξ q.val)))*
      Real.sqrt (Z^(rightExponent A (geometryExponents s modifier R seed K Z ξ r.val))) ≤
        32*Z^M := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s modifier R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := cross_exponent_payment
    (geometryExponents s modifier R seed K Z ξ q.val)
    (geometryExponents s modifier R seed K Z ξ q.val)
    (geometryExponents s modifier R seed K Z ξ r.val) M A (Real.logb Z 2) hw
    (fun i => ⟨by simpa using hw,by simpa using hw⟩)
    (fun i => ⟨hdiff r q i,hdiff q r i⟩)
    (actual_geometry_balance s modifier R seed K Z ξ M A hZ q.val)
  have hp : Z^(M+5*Real.logb Z 2)=32*Z^M := by
    rw [Real.rpow_add hz,show 5*Real.logb Z 2=Real.logb Z 2*5 by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [←hp]
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_fiber_difference
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_balance
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_cross_payment
