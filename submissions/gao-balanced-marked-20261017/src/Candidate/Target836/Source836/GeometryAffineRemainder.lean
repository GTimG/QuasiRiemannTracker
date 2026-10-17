import Candidate.Target836.Source836.GlobalNamed
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRemainder
import Candidate.Target836.Source836.GeometryMainRemainder
import Candidate.Target836.Source836.ZeroScalar
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target836.Error836.GeometryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction
import Candidate.Target836.Source836.GeometryAffineExceptionalGates

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The small losses in the width-one zero term leave a fixed strict saving. -/
theorem geometry_affine_zero_loss (Z μ A beta : ℝ)
    (hμ : 0<μ) (hcap : μ≤1/128) (hA : A≤3)
    (hb : 3401/100000≤beta ∧ beta≤1/25)
    (hω : frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128) :
    zeroPaymentExponent Z 1 A (GlobalNamed.amp beta) (μ/64) (μ/8)
      (μ/128) (μ/128) (μ/128) 3+3*(μ/128)≤-(1/20:ℝ) := by
  have hpaid := Target836ErrorPayment.geometry_zero_exponent_saving Z 1 A (GlobalNamed.amp beta)
    (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3 (μ/128) beta
    (by norm_num) hb (by simp)
  have hmul := mul_le_mul_of_nonneg_left hA (show 0≤μ/128 by positivity)
  have hsq : μ*(μ/128)≤μ := by
    have hh : μ/128≤1 := by linarith
    exact (mul_le_mul_of_nonneg_left hh hμ.le).trans_eq (mul_one μ)
  have hbudget : frequencyLoss Z 32 (μ/64)+μ/8+
      μ/128*(A+μ/128)+3*(μ/128)+3*(μ/128)≤1/380 := by nlinarith
  simpa only [zeroPaymentExponent, Cycle63InitialMass.zeroPaymentExponent, neg_div] using hpaid hbudget

/-- Genuine source and cone receipts pay the complete zero and tail terms.
Only the exact retained sum remains on the right, before its low/high split. -/
theorem eventual_actual_affine_main_remainder
    (Cs μ : ℝ) (hCs : 1≤Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,3401/100000≤beta ∧ beta≤1/25 →
      Real.logb Z (volume s)≤GlobalNamed.totalA beta →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      geometryAffineMainSourceTotal s Ψ Z (GlobalNamed.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (GlobalNamed.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_main_remainder (ι:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128) 1
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+zconst+tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop ((9/4:ℝ)^(Fintype.card ι)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps beta hb hcone Ψ t reflected key
  have ha := (GlobalNamed.amp_pos hb).le
  have haB : GlobalNamed.amp beta≤3 := (GlobalNamed.amp_bounds hb).2.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (GlobalNamed.amp beta) (μ/8) (μ/128) t hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) hpad squarefree_one one_ne_zero caps.sourcePositive caps.sourceCap
    caps.volumeLog caps.poolCap reflected key
  have hz := geometry_affine_zero_loss Z μ (Real.logb Z (volume s)) beta hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -(1:ℝ)≤-(1/20:ℝ))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hzconst : 0≤zconst := by dsimp [zconst];positivity
  have htconst : 0≤tconst := by dsimp [tconst];positivity
  have h₁ := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)
  have h₂ := mul_le_mul_of_nonneg_left htail
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(1/20:ℝ)) := by positivity
  simp only [map_one,Nat.cast_one,div_one] at hh
  have hnorm : geometryAffineMainSourceTotal s Ψ Z (GlobalNamed.amp beta) (μ/64) (μ/8)
      t hZ reflected key≤
      zconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (GlobalNamed.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (GlobalNamed.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineMainSourceTotal,geometryMainRetainedSum,
        geometryLowFirstWeight,geometryLowFirstChild,Fintype.sum_sigma,zconst,tconst,
        original,OriginalData.columns,OriginalData.beta,OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,one_mul]; ring
  nlinarith

end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.geometry_affine_zero_loss
#print axioms OAI.SevenEighths.Target836SourceAssembly.eventual_actual_affine_main_remainder
