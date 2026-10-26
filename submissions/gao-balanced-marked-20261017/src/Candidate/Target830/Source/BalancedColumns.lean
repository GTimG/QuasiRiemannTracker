import Candidate.Cycle63.Physical.InitialMass.ActiveColumns
import Candidate.Cycle63.Physical.InitialMass.JointWindowEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometrySources
import Candidate.Target830.Source.BalancedPayment

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentLogDyadic
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
open Cycle63InitialMass

theorem actual_geometry_seed (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (q : CommonGeometryFiber s R seed K Z ξ key) :
    seed∣(geometryFirstSource s R seed K Z ξ hK key q).C ∧
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).D := by
  have hh := actual_common_gates s R seed hs hz₁ hz₂ q.val.1.val.1 q.val.1.val.2 q.val.1.property
  exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩

open Cycle63InitialMass

def balancedColumnScalar (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  Cycle63InitialMass.geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j*
    ((Z^(-surplus (geometryExponents s R seed K Z ξ j.1.val)/2):ℝ):ℂ)

/-- Literal live child-source budget for one side of the first transform.
No estimate of its main, error, low or high branch is assumed here. -/
def balancedLiveBudget (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (b t : ℝ) : ℝ :=
  let src := geometryFirstSource s R seed K Z ξ hK key
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key
  let τ := geometryColumnCharacter reflected s R seed K Z ξ hK key
  ∑j∈firstLiveColumns src (fun _=>logAnnulus),
    ‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
      ((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
        ∑B : actualAllocations s.pools (C j),
          if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R j.2.1.val B
              (τ j) t CenteredMomentFirstAnnularMajorant.profile (src j.1).H0
          else 0)

theorem actual_balanced_source_budget (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b t : ℝ) (ha : 0<a) (hcard : Fintype.card ι≤N)
    (haS : a≤s.lower) (hbS : s.upper≤b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :
    let src := geometryFirstSource s R seed K Z ξ hK key
    let C := geometryColumnIdeal reflected s R seed K Z ξ hK key
    let τ := geometryColumnCharacter reflected s R seed K Z ξ hK key
    (∑q∈firstActiveSectors src (fun _=>logAnnulus),
      ‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight (firstSectorColumn src q)*
        allocatedPolynomial (original s R seed) (C (firstSectorColumn src q)) q.2.1.val
          (τ (firstSectorColumn src q)) t (volume s) (firstSignedRow reflected q.2.2.2.2.val)‖^2)≤
      balancedLiveBudget reflected s R seed K Z ξ M A hK key weight N b t := by
  intro src C τ
  have hC (j : FirstColumnIndex src) : Supported (C j) := by
    cases reflected
    · exact (src j.1).hC
    · exact (src j.1).hD
  have hseed (j : FirstColumnIndex src) : seed∣C j := by
    have hh := actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ j.1
    cases reflected
    · exact hh.1
    · exact hh.2
  have hh := actual_active_common_live_energy reflected src N a b ha s hcard haS hbS C R seed
    hC hseed τ (fun _=>t)
    (fun j=>‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2)
    (fun _=>sq_nonneg _)
  simpa only [norm_mul,mul_pow,balancedLiveBudget,src,C,τ] using hh


theorem balancedColumnScalar_norm_sq (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) (hZ : 0<Z) :
    ‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2=
      ‖Cycle63InitialMass.geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
        Z^(-surplus (geometryExponents s R seed K Z ξ j.1.val)) := by
  have hp (v : ℝ) : (Z^(-v/2))^2=Z^(-v) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  simp only [balancedColumnScalar,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le _),hp]

end
end OAI.SevenEighths.Target830.Source

#print axioms OAI.SevenEighths.Target830.Source.balancedColumnScalar_norm_sq
#print axioms OAI.SevenEighths.Target830.Source.actual_balanced_source_budget
