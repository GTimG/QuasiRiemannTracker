import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorCoprime
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FirstBranches.FixedComparison
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.AmplifierSupport
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimePool CenteredMomentAmplificationSlotGap CenteredMomentAmplificationEligibility
open CenteredMomentPrimeElements CompletedGauss
local notation "O" => HeckeFamily.O

/-- The analytic mesh is fixed before a chosen slot dictionary or its size. -/
def geometryAnalyticMesh (Mmin Mmax εaffine Mcap Bmask L : ℝ) : ℝ :=
  let μ:=geometryLossUnit Mmin εaffine
  min (Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine)
    (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*Cycle63.AffineLedger.amplifierFloor/4)))/2

theorem geometry_analytic_mesh_admission (Mmin Mmax εaffine Mcap Bmask L : ℝ)
    (hmin : 0<Mmin)(hmax : Mmin≤Mmax)(hε : 0<εaffine)
    (hcap : 0<Mcap)(hmask : 0≤Bmask) :
    let μ:=geometryLossUnit Mmin εaffine
    let mesh:=geometryAnalyticMesh Mmin Mmax εaffine Mcap Bmask L
    0< mesh ∧ mesh≤Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine ∧
      mesh≤Cycle25.Energy.commonMesh Mcap Bmask L (μ/8) ∧ mesh≤μ/8 ∧
      mesh<Mmin*Cycle63.AffineLedger.amplifierFloor/2 := by
  intro μ mesh
  have hu : 0<μ := geometry_loss_unit_pos Mmin εaffine hmin hε
  have hc := Cycle63FirstActual.comparisonMesh_pos Mmin Mmax εaffine hmin hmax hε
  have ho := Cycle25.Energy.commonMesh_pos Mcap Bmask L (μ/8) hcap.le hmask (by positivity)
  have hfl := Cycle63.AffineLedger.amplifierFloor_pos
  have hm : 0< mesh := by dsimp [mesh,geometryAnalyticMesh];change 0< min _ (min _ (min (μ/8) _))/2;positivity
  have ha : 2*mesh≤Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine := by
    dsimp [mesh,geometryAnalyticMesh];linarith [min_le_left
      (Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine)
      (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8)) (min (μ/8) (Mmin*Cycle63.AffineLedger.amplifierFloor/4)))]
  have ht : 2*mesh≤ min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*Cycle63.AffineLedger.amplifierFloor/4)) := by
    dsimp [mesh,geometryAnalyticMesh];linarith [min_le_right
      (Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine)
      (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8)) (min (μ/8) (Mmin*Cycle63.AffineLedger.amplifierFloor/4)))]
  have hb := ht.trans (min_le_left _ _)
  have hd := ht.trans (min_le_right _ _)
  have he := hd.trans (min_le_left _ _)
  have hf := hd.trans (min_le_right _ _)
  refine ⟨hm,?_,?_,?_,?_⟩ <;> linarith

variable (rayM : Ideal O) [NeZero rayM]
local instance meshFiniteQuotient : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
