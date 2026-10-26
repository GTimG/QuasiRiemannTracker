import Candidate.Target830.Source.BalancedAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryMainNormalized

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem balancedAllocationWeight_eq (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    balancedAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B=
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B*
        Z^(-surplus (geometryExponents s R seed K Z ξ j.1.val)) := by
  unfold balancedAllocationWeight geometryAllocationWeight
  dsimp only
  split_ifs
  · rw [balancedColumnScalar_norm_sq reflected s R seed K Z ξ M A hK key weight j hZ]
    ring
  · simp only [zero_mul]

/-- The first weight is the actual balanced allocation mass divided by
the unchanged child volume. -/
def balancedLowFirstWeight (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) : ℝ :=
  balancedAllocationWeight reflected s R seed K Z ξ M A hK bin weight (Fintype.card α) b q.1.val q.2/
    volume (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q)

theorem balancedLowFirstWeight_eq (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    balancedLowFirstWeight reflected s R seed K Z ξ M A hK bin weight b t q=
      geometryLowFirstWeight reflected s R seed K Z ξ M A hK bin weight b t q*
        Z^(-surplus (geometryExponents s R seed K Z ξ q.1.val.1.val)) := by
  unfold balancedLowFirstWeight geometryLowFirstWeight
  rw [balancedAllocationWeight_eq reflected s R seed K Z ξ M A hK hZ bin weight
    (Fintype.card α) b q.1.val q.2]
  ring

theorem balancedLowFirstWeight_nonneg (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    0≤balancedLowFirstWeight reflected s R seed K Z ξ M A hK bin weight b t q :=
  div_nonneg (balancedAllocationWeight_nonneg reflected s R seed K Z ξ M A hK bin weight
    (Fintype.card α) b q.1.val q.2) (volume_pos _).le

section Second
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
def balancedMainSecondWeight (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) : ℂ :=
  (balancedLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1:ℂ)*
  actualSecondBlockWeight
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j.1)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val)
    j.1.1.val.2.1.val
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val)) Z ξ j.2

theorem balancedMainSecondWeight_eq (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    balancedMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j=
      geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*
        ((Z^(-surplus (geometryExponents s R seed (Z^Mrow) Z ξ j.1.1.val.1.val)):ℝ):ℂ) := by
  unfold balancedMainSecondWeight geometryMainSecondWeight
  rw [balancedLowFirstWeight_eq reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (zero_lt_one.trans hZ) key weight b t j.1]
  push_cast
  ring

end Second
end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.balancedAllocationWeight_eq
#print axioms OAI.SevenEighths.Target830.Source.balancedLowFirstWeight_eq
#print axioms OAI.SevenEighths.Target830.Source.balancedLowFirstWeight_nonneg
#print axioms OAI.SevenEighths.Target830.Source.balancedMainSecondWeight_eq
