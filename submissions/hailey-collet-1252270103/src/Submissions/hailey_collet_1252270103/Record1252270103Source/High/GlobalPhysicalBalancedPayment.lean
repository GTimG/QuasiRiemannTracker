/- Adapted from Zhongpai Gao, gao-balanced-marked-20261017, Apache-2.0;
upstream math snapshot 9c0e14f985041e397f71c574028193ee595a0f98.
Underlying Cycle61: Hailey Collet; original analytic interfaces: OpenAI, Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalGeometryPayment
import Submissions.hailey_collet_1252270103.Record12518109Assembly.BalancedPayment
import Submissions.hailey_collet_1252270103.Record12518109Assembly.BalancedGeometry
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.Normalization

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O

open Cycle61InitialMass

open QRH.Record12518109Assembly
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem actual_surplus_nonneg (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (hZ : 1<Z) (q : SourceCoordinate s modifier R seed K Z ξ) :
    0 ≤ surplus (geometryExponents s modifier R seed K Z ξ q) := by
  have hh := actual_geometry_balance s modifier R seed K Z ξ 0 0 hZ q
  have he := QRH.Record12518109Assembly.Scalar.old_budget 0 0
    (geometryExponents s modifier R seed K Z ξ q 0)
    (geometryExponents s modifier R seed K Z ξ q 1)
    (geometryExponents s modifier R seed K Z ξ q 3)
    (geometryExponents s modifier R seed K Z ξ q 4)
    (geometryExponents s modifier R seed K Z ξ q 2)
  change outsideExponent 0 0 (geometryExponents s modifier R seed K Z ξ q)+
    (leftExponent 0 (geometryExponents s modifier R seed K Z ξ q)+
      rightExponent 0 (geometryExponents s modifier R seed K Z ξ q))/2=
        0-surplus (geometryExponents s modifier R seed K Z ξ q) at he
  rw [he] at hh
  linarith

omit [DecidableEq ι] in
/-- Uniform cross-label payment. The left and right labels may differ;
no sum of per-label Cauchy estimates is substituted for joint Cauchy. -/
theorem actual_balanced_cross_payment (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q r : CommonGeometryFiber s modifier R seed K Z ξ key) :
    Z^(outsideExponent M A (geometryExponents s modifier R seed K Z ξ q.val))*
      Real.sqrt (Z^(balancedLeft A (geometryExponents s modifier R seed K Z ξ q.val)))*
      Real.sqrt (Z^(balancedRight A (geometryExponents s modifier R seed K Z ξ r.val))) ≤
        4*Z^M := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s modifier R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := QRH.Record12518109Assembly.Scalar.cross_label_budget
    (m := M) (a := A)
    (c := geometryExponents s modifier R seed K Z ξ q.val 0)
    (d := geometryExponents s modifier R seed K Z ξ q.val 1)
    (r := geometryExponents s modifier R seed K Z ξ q.val 3)
    (e := geometryExponents s modifier R seed K Z ξ q.val 4)
    (c' := geometryExponents s modifier R seed K Z ξ r.val 0)
    (d' := geometryExponents s modifier R seed K Z ξ r.val 1)
    (r' := geometryExponents s modifier R seed K Z ξ r.val 3)
    (e' := geometryExponents s modifier R seed K Z ξ r.val 4)
    (w := Real.logb Z 2)
    (abs_le.mpr ⟨by linarith [hdiff q r 0],hdiff r q 0⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 1],hdiff r q 1⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 3],hdiff r q 3⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 4],hdiff r q 4⟩)
  change outsideExponent M A (geometryExponents s modifier R seed K Z ξ q.val)+
    (balancedLeft A (geometryExponents s modifier R seed K Z ξ q.val)+
      balancedRight A (geometryExponents s modifier R seed K Z ξ r.val))/2≤M+2*Real.logb Z 2 at he
  have hp : Z^(M+2*Real.logb Z 2)=4*Z^M := by
    rw [Real.rpow_add hz,show 2*Real.logb Z 2=Real.logb Z 2*2 by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [←hp]
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith


omit [DecidableEq ι] in
/-- The actual first scalar stays on the left of joint Cauchy. Normalized
left and right energies are still summed over every label in the bin. -/
theorem actual_balanced_joint_energy {I J : Type*} [Fintype I] [Fintype J] (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ))
    (left : I→CommonGeometryFiber s modifier R seed K Z ξ key)
    (right : J→CommonGeometryFiber s modifier R seed K Z ξ key) (L : I→ℝ) (N : J→ℝ)
    (hL : ∀q,0≤L q) (hN : ∀q,0≤N q) :
    Real.sqrt (∑q,Z^(2*outsideExponent M A (geometryExponents s modifier R seed K Z ξ (left q).val)+
        balancedLeft A (geometryExponents s modifier R seed K Z ξ (left q).val))*L q)*
      Real.sqrt (∑q,Z^(balancedRight A (geometryExponents s modifier R seed K Z ξ (right q).val))*N q) ≤
        4*Z^M*Real.sqrt (∑q,L q)*Real.sqrt (∑q,N q) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  apply weighted_joint_energy _ _ _ _ _ (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) hL hN (by positivity)
  intro q r
  have hh := actual_balanced_cross_payment s modifier R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key (left q) (right r)
  have hsquared := pow_le_pow_left₀ (by positivity) hh 2
  rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
    Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
    ←Real.rpow_add hz] at hsquared
  convert hsquared using 1
  congr 2
  ring

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_surplus_nonneg
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_cross_payment
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_joint_energy
