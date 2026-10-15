import Candidate.Cycle62.Physical.InitialMass.GeometryLowAdmission

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle62Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open Cycle62FinalLow
open Cycle62Moment.LowBranch Cycle62FinalNatural Cycle62FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle62FinalProfiles
local notation "O" => HeckeFamily.O
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _



/-- The first projector divides both ideals in the literal second block. -/
theorem actual_geometry_low_column_seed (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    d.seed∣d.C ∧ d.seed∣d.D := by
  exact (actual_retained_block_gates (liveIndices q.2.val)
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ
    (first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _) n) |>.imp_right (fun h=>h.1)

section Column
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
set_option quotPrecheck false in
local notation "d" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
set_option quotPrecheck false in
local notation "firstChild" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
variable (second : Bool)
/-- A literal child identification rewrites the complete low column sum.
It leaves the common allocation fixed and imposes no energy hypothesis. -/
theorem actual_geometry_low_column_sum (χ : RayFourExpansion.RayCharacter) (v : ℝ)
    (actualChild : Input (liveIndices q.2.val))
    (hchild : actualChild=withHeight firstChild ((d).τ χ) v)
    (Ds : Finset (Ideal O)) (zs : Finset O) (weight : O→ℝ)
    (hE : Supported (if second then (d).D else (d).C)) :
    (∑D∈Ds,∑z∈zs,weight z*
      ‖normalizedColumn actualChild (if second then (d).D else (d).C) hE (d).R (d).seed D z‖^2)=
    (∑D∈Ds,∑z∈zs,weight z*
      ‖normalizedColumn (withHeight firstChild ((d).τ χ) v)
        (if second then (d).D else (d).C) hE (d).R (d).seed D z‖^2) := by
  rw [hchild]


end Column
end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_low_column_seed
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_low_column_sum
