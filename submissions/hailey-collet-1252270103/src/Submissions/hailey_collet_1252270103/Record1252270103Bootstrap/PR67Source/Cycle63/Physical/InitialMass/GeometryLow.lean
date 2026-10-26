import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowProfiles
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryWidth
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open Cycle63FinalLow
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Build the low-estimate geometry from the actual first geometric
column and any actual live second row. The selected allocations remain
literal; no moment estimate or whole-block nonvanishing is supplied. -/
def actualGeometryLow (reflected : Bool)(s : Input α)(q : Chain s)
    (R seed : Ideal O)(Z Mrow amp ξ reserve b : ℝ)(N : ℕ)(hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin))
    (hC : q.C₁=geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j)
    (hη : q.η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j)
    (d : SecondInputDatum α)(r : secondLiveRows (fun _:Unit=>d.block))
    (hparent : d.input.η=q.η₁)
    (hradius : d.radius=frequencyRadius
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j)) Z ξ)
    (hlabel : q.E₂=d.C ∨ q.E₂=d.D)
    (hf₁ : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0) :
    LiveMainGeometry s q Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b N :=
  let src := geometryFirstSource s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1
  { reflected:=reflected,C₀:=src.C,D₀:=src.D,hC₀:=src.hC,hD₀:=src.hD,
    heq₀:=src.sameSupport,selected:=hC,E₀:=src.inactive,
    hmod:=by
      rw [hη]
      exact actual_geometry_column_modulus reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j,
    δ:=frequencyLoss Z 32 ξ,reserve:=reserve,homega:=rfl,
    datum:=d,parent:=hparent,row:=r,radius_eq:=hradius,label:=hlabel,
    first_nonzero:=hf₁,second_nonzero:=hf₂ }

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
