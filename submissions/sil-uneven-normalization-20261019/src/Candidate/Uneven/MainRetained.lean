/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.SecondWeight
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open OAI.SevenEighths.Target830.Source.Uneven
open Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile CenteredMomentLogDyadic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance mainOrdinaryContractionSumDecidable {ι : Type*} :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "N" => Fintype.card α
local notation "firsts" => GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
local notation "blocks" => geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂

/-- The literal joint main retained sum: first allocation weight, child seed,
original puncture and second Fourier scales are unchanged. -/
def unevenMainRetainedSum (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) : ℂ :=
  ∑q : firsts,
    (unevenLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t q:ℂ)*
    secondRetainedEnergy
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).η
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).t
      (finiteColumns (Fintype.piFinset (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).pools))
      (coefficient (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)
        (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) q.1.val.2.1.val)
      ballProfile
      (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val))
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)) Z ξ

/-- Original full-block filtering precedes the inducing split. -/
theorem actual_main_retained_nonzero_sum (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) :
    unevenMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key Mprice Aprice weight =
      ∑j : blocks,
        unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val*
        (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          j.val.1 hz₁ hz₂ j.val.2).block.value ballProfile := by
  have hassembly := actual_joint_retained_assembly
    (fun q : firsts=>liveIndices q.2.val)
    (fun q=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)
    (fun q=>R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)
    (fun q=>q.1.val.2.1.val)
    (fun q=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus) q.1.val q.1.property)
    (fun _=>hz₁) (fun _=>hz₂) ballProfile
    (fun q=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val))
    (fun q=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)) Z ξ
    (fun q=>first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _)
    (fun q=>(unevenLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t q:ℂ))
  have heq : unevenMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key Mprice Aprice weight =
      ∑j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key,
        unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*
        (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          j.1 hz₁ hz₂ j.2).block.value ballProfile := by
    simpa only [unevenMainRetainedSum,unevenMainSecondWeight,geometryLowSecondDatum] using hassembly
  rw [heq]
  let datum := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block
  let coeff := unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight
  let live := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0
  conv_rhs => rw [Finset.sum_coe_sort blocks (fun j=>coeff j*(datum j).value ballProfile)]
  conv_rhs => rw [geometryMainNonzeroBlocks,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rfl
  · by_cases hlive : live j
    · have hz : (datum j).value ballProfile=0 := by
        by_contra hn
        exact h ⟨hlive,hn⟩
      rw [hz,mul_zero]
    · have hw : coeff j=0 := by
        simp only [coeff,unevenMainSecondWeight,unevenLowFirstWeight,unevenAllocationWeight,
          live] at hlive ⊢
        simp only [hlive,ite_false,zero_div,Complex.ofReal_zero,zero_mul]
      change coeff j*(datum j).value ballProfile=0
      rw [hw,zero_mul]

end Actual
end
end OAI.SevenEighths.MainAssembly
