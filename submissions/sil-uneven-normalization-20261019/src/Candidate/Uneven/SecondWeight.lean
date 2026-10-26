/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/
import Candidate.Uneven.Amplification
import Candidate.Cycle63.Physical.InitialMass.GeometryMainNormalized

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Uneven
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

theorem unevenAllocationWeight_eq (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B=
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B*
        Z^(-allocation reflected (geometryExponents s R seed K Z ξ j.1.val)) := by
  unfold unevenAllocationWeight geometryAllocationWeight
  dsimp only
  split_ifs
  · rw [unevenColumnScalar_norm_sq reflected s R seed K Z ξ M A hK key weight j hZ]
    ring
  · simp only [zero_mul]

/-- The first weight is the actual uneven allocation mass divided by
the unchanged child volume. -/
def unevenLowFirstWeight (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) : ℝ :=
  unevenAllocationWeight reflected s R seed K Z ξ M A hK bin weight (Fintype.card α) b q.1.val q.2/
    volume (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q)

theorem unevenLowFirstWeight_eq (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    unevenLowFirstWeight reflected s R seed K Z ξ M A hK bin weight b t q=
      geometryLowFirstWeight reflected s R seed K Z ξ M A hK bin weight b t q*
        Z^(-allocation reflected (geometryExponents s R seed K Z ξ q.1.val.1.val)) := by
  unfold unevenLowFirstWeight geometryLowFirstWeight
  rw [unevenAllocationWeight_eq reflected s R seed K Z ξ M A hK hZ bin weight
    (Fintype.card α) b q.1.val q.2]
  ring


section Second
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
def unevenMainSecondWeight (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) : ℂ :=
  (unevenLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
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

theorem unevenMainSecondWeight_eq (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j=
      geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*
        ((Z^(-allocation reflected (geometryExponents s R seed (Z^Mrow) Z ξ j.1.1.val.1.val)):ℝ):ℂ) := by
  unfold unevenMainSecondWeight geometryMainSecondWeight
  rw [unevenLowFirstWeight_eq reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (zero_lt_one.trans hZ) key weight b t j.1]
  push_cast
  ring

end Second
end
end OAI.SevenEighths.Target830.Source.Uneven
