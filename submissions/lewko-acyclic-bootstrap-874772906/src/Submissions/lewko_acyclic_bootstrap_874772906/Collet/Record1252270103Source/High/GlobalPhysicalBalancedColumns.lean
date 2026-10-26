/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified first live columns, exact allocation weights and dyadic bands. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBalancedWindows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalAnnular
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentLogDyadic CenteredMomentFirstCanonicalFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentAddedZeroUniform
open Cycle61InitialMass QRH.Record12518109Assembly
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
theorem actual_geometry_seed (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (q : CommonGeometryFiber s modifier R seed K Z ξ key) :
    seed∣(geometryFirstSource s modifier R seed K Z ξ hK key q).C ∧
      seed∣(geometryFirstSource s modifier R seed K Z ξ hK key q).D := by
  have hh := actual_common_gates s modifier R seed hs hz₁ hz₂ q.val.1.val.1 q.val.1.val.2 q.val.1.property
  exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩

def geometryColumnIdeal (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK key)) : Ideal O :=
  if reflected then (geometryFirstSource s modifier R seed K Z ξ hK key j.1).D
    else (geometryFirstSource s modifier R seed K Z ξ hK key j.1).C

def geometryColumnCharacter (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK key)) : Character :=
  let src := geometryFirstSource s modifier R seed K Z ξ hK key j.1
  let pair := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  if reflected then pair.right else pair.left

def balancedColumnScalar (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK key)) : ℂ :=
  if reflected then
    (Real.sqrt (Z^(balancedRight A (geometryExponents s modifier R seed K Z ξ j.1.val))):ℂ)⁻¹
  else weight j.1.val*(geometryFirstSource s modifier R seed K Z ξ hK key j.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s modifier R seed K Z ξ j.1.val)+
      balancedLeft A (geometryExponents s modifier R seed K Z ξ j.1.val))):ℂ)


/-- Literal full allocation energy. Frozen zero coefficients are retained
as zero weights and every original live column remains inside the sum. -/
def balancedLiveBudget (reflected : Bool) (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ) (t : ℝ) : ℝ :=
  let src:=geometryFirstSource s modifier R seed K Z ξ hK key
  let C:=geometryColumnIdeal reflected s modifier R seed K Z ξ hK key
  let τ:=geometryColumnCharacter reflected s modifier R seed K Z ξ hK key
  ∑j∈firstLiveColumns src (fun _=>logAnnulus),
    ‖balancedColumnScalar reflected s modifier R seed K Z ξ M A hK key weight j‖^2*
      ∑n∈bands (src j.1).H0, ((actualAllocations s.pools (C j)).card:ℝ)*
        ∑B:actualAllocations s.pools (C j),‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*
          (∑'z:O,dyadicWeight n (normValue z)*
            ‖childPolynomial s modifier (C j) R j.2.1.val B (τ j) t (volume s) z‖^2)

theorem actual_balanced_source_budget (reflected : Bool) (s : Input ι)
    (modifier : Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ) (t : ℝ) :
    let src:=geometryFirstSource s modifier R seed K Z ξ hK key
    let C:=geometryColumnIdeal reflected s modifier R seed K Z ξ hK key
    let τ:=geometryColumnCharacter reflected s modifier R seed K Z ξ hK key
    (∑q∈firstActiveSectors src (fun _=>logAnnulus),
      ‖balancedColumnScalar reflected s modifier R seed K Z ξ M A hK key weight
          (firstSectorColumn src q)*
        allocatedPolynomial (original s R seed) modifier (C (firstSectorColumn src q))
          q.2.1.val (τ (firstSectorColumn src q)) t (volume s)
          (firstSignedRow reflected q.2.2.2.2.val)‖^2)≤
      balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key weight t := by
  intro src C τ
  simp only [norm_mul,mul_pow]
  have he := actual_first_live_columns src (fun _=>logAnnulus)
    (fun j z=>‖balancedColumnScalar reflected s modifier R seed K Z ξ M A hK key weight j‖^2*
      ‖allocatedPolynomial (original s R seed) modifier (C j) j.2.1.val (τ j) t
        (volume s) (firstSignedRow reflected z)‖^2)
  apply le_trans (le_of_eq he)
  unfold balancedLiveBudget
  apply Finset.sum_le_sum
  intro j hj
  rw [←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (finite_signed_annular_energy_le_bands reflected
    (allocatedPolynomial (original s R seed) modifier (C j) j.2.1.val (τ j) t (volume s))
    (src j.1).H0 (src j.1).H0_pos (firstColumnRows src (fun _=>logAnnulus) j)
    (actual_first_column_annulus src j)).trans
  exact Finset.sum_le_sum (fun n _=>GlobalPhysical.actual_allocation_dyadic_energy s modifier
    (C j) R seed j.2.1.val (τ j) t (volume s) n)

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_seed
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_source_budget
