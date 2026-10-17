import Candidate.Target830.Source.CellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRemainder
import Candidate.Target830.Source.Assembly.BalancedMainRemainder
import Candidate.Target830.Source.Assembly.BalancedRetained
import Candidate.Target830.Source.Reconstruction.ZeroScalar
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target830.Source.Reconstruction.GeometryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction
import Candidate.Target830.Source.Reconstruction.GeometryAffineExceptionalGates

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open Reconstruction
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
variable {plane : SourcePlane}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The main source before retained contraction, with the original allocation
weights and the actual slot cardinality in its Fourier scale. -/
def balancedAffineMainSourceTotal (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let phase := fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
  ∑q : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key,
    balancedAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2 *
    actualMainSource (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key t q)
      (geometryBranch reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key q.1.val) Z (3*amp) 1 ξ reserve

/-- The small losses in the width-one zero term leave a fixed strict saving. -/
theorem geometry_affine_zero_loss (Z μ A beta : ℝ)
    (hμ : 0<μ) (hcap : μ≤1/128) (hA : A≤3)
    (hb : widthLower≤beta ∧ beta≤widthUpper)
    (hω : frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128) :
    Reconstruction.zeroPaymentExponent Z 1 A (plane.amp beta) (μ/64) (μ/8)
      (μ/128) (μ/128) (μ/128) 3+3*(μ/128)≤-(1/20:ℝ) := by
  have hpaid := geometry_zero_exponent_saving (plane:=plane) Z 1 A (plane.amp beta)
    (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3 (μ/128) beta
    (by norm_num) hb (by simp)
  have hmul := mul_le_mul_of_nonneg_left hA (show 0≤μ/128 by positivity)
  have hsq : μ*(μ/128)≤μ := by
    have hh : μ/128≤1 := by linarith
    exact (mul_le_mul_of_nonneg_left hh hμ.le).trans_eq (mul_one μ)
  have hbudget : frequencyLoss Z 32 (μ/64)+μ/8+
      μ/128*(A+μ/128)+3*(μ/128)+3*(μ/128)≤1/380 := by nlinarith
  simpa only [Reconstruction.zeroPaymentExponent, Cycle63InitialMass.zeroPaymentExponent, neg_div] using hpaid hbudget

/-- Genuine source and cone receipts pay the complete zero and tail terms.
Only the exact retained sum remains on the right, before its low/high split. -/
theorem eventual_actual_affine_main_remainder
    (Cs μ : ℝ) (hCs : 1≤Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,widthLower≤beta ∧ beta≤widthUpper →
      Real.logb Z (volume s)≤plane.total beta →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      balancedAffineMainSourceTotal s Ψ Z (plane.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 (plane.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_main_remainder (plane:=plane) (ι:=ι)
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
  have ha := (Source.amplifier_pos plane hb).le
  have haB : plane.amp beta≤3 := (Source.source_guards plane hb).2.2.2.1.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (plane.amp beta) (μ/8) (μ/128) t hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) hpad squarefree_one one_ne_zero caps.sourcePositive caps.sourceCap
    caps.volumeLog caps.poolCap reflected key
  have hz := geometry_affine_zero_loss (plane:=plane) Z μ (Real.logb Z (volume s)) beta hμ hcap
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
  have hnorm : balancedAffineMainSourceTotal s Ψ Z (plane.amp beta) (μ/64) (μ/8)
      t hZ reflected key≤
      zconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(Reconstruction.zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (plane.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 (plane.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
    convert hh using 1 <;>
      simp only [balancedAffineMainSourceTotal,balancedMainRetainedSum,
        balancedLowFirstWeight,geometryLowFirstChild,Fintype.sum_sigma,zconst,tconst,
        original,OriginalData.columns,OriginalData.beta,OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,one_mul]; ring
  nlinarith

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.geometry_affine_zero_loss
#print axioms OAI.SevenEighths.Target830.Source.Assembly.eventual_actual_affine_main_remainder
