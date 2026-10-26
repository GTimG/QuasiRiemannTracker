import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The mesh of the second step of the two-level ledger and the slot mesh of the first step that it admits: the
affine loss, the loss unit and the old loss of the second step, early in the import order. Released under
Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The affine loss of the schedule of the second step. The dictionary rate of a schedule with `n` slots is at most its
loss unit over `2048 (n + 1)`, so the losses of the second step are bounded independently of `n`. -/
def secondStepAffineLoss : ℝ := 1 / 10 ^ 10

/-- The loss unit of the schedule of the second step. -/
def secondStepLossUnit : ℝ := geometryLossUnit 1 secondStepAffineLoss

/-- The loss of the old moment in the unit of the second step: the loss `εold = μ/8` of the first level, with the
loss unit `μ` of the first level of affine loss `εaffine`, divided by the largest width `101/100` of a state. -/
def secondStepOldLoss (εaffine : ℝ) : ℝ := geometryLossUnit 1 εaffine / 8 / (101 / 100)

/-- The mesh of the second step: the least of the bounds of the slot widths of the generic step and the HIGH given.
A quarter of the weight of the LOW reserve is below half the amplifier floor of every ledger of the grid; the common
meshes are those of the dictionary of the second step with the masks `28 + 20` and `28`, and of the old moment of the
loss `secondStepOldLoss εaffine / 2` in the unit of a state with mask `20`. -/
def secondStepMesh (εaffine : ℝ) : ℝ :=
  min (Cycle63.Optimization.lowReserveWeight / 4)
    (min (Cycle25.Energy.commonMesh 2 (28 + 20) 1 (secondStepLossUnit / 8))
      (min (Cycle25.Energy.commonMesh 2 28 1 (secondStepLossUnit / 8))
        (Cycle25.Energy.commonMesh 1 20 1 (secondStepOldLoss εaffine / 2))))

theorem secondStepAffineLoss_pos : 0 < secondStepAffineLoss := by
  unfold secondStepAffineLoss
  positivity

theorem secondStepLossUnit_pos : 0 < secondStepLossUnit :=
  geometry_loss_unit_pos 1 _ one_pos secondStepAffineLoss_pos

theorem secondStepLossUnit_le : secondStepLossUnit ≤ secondStepAffineLoss / 128 :=
  min_le_left _ _

theorem secondStepOldLoss_pos {εaffine : ℝ} (hε : 0 < εaffine) : 0 < secondStepOldLoss εaffine := by
  have h := geometry_loss_unit_pos 1 εaffine one_pos hε
  unfold secondStepOldLoss
  positivity

theorem secondStepMesh_pos {εaffine : ℝ} (hε : 0 < εaffine) : 0 < secondStepMesh εaffine := by
  have hμ := secondStepLossUnit_pos
  have hc := secondStepOldLoss_pos hε
  unfold secondStepMesh
  refine lt_min (by have := Cycle63.Optimization.lowReserveWeight_pos; linarith) (lt_min ?_ (lt_min ?_ ?_))
  · exact Cycle25.Energy.commonMesh_pos 2 (28 + 20) 1 _ (by norm_num) (by norm_num) (by positivity)
  · exact Cycle25.Energy.commonMesh_pos 2 28 1 _ (by norm_num) (by norm_num) (by positivity)
  · exact Cycle25.Energy.commonMesh_pos 1 20 1 _ (by norm_num) (by norm_num) (by positivity)

theorem secondStepMesh_le_reserveWeight (εaffine : ℝ) :
    secondStepMesh εaffine ≤ Cycle63.Optimization.lowReserveWeight / 4 :=
  min_le_left _ _

theorem secondStepMesh_le_dictionary (εaffine : ℝ) :
    secondStepMesh εaffine ≤ Cycle25.Energy.commonMesh 2 (28 + 20) 1 (secondStepLossUnit / 8) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem secondStepMesh_le_producer (εaffine : ℝ) :
    secondStepMesh εaffine ≤ Cycle25.Energy.commonMesh 2 28 1 (secondStepLossUnit / 8) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem secondStepMesh_le_oldMoment (εaffine : ℝ) :
    secondStepMesh εaffine ≤ Cycle25.Energy.commonMesh 1 20 1 (secondStepOldLoss εaffine / 2) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- The slot mesh of the first step that the second step admits, for the affine loss `εaffine` of the first step:
the common mesh of the width cap `101/100` of row 5 and `2/5` of the mesh of the second step. -/
def twoLevelSlotMesh (εaffine : ℝ) : ℝ :=
  min (Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8)) (2/5*secondStepMesh εaffine)

theorem twoLevelSlotMesh_pos {εaffine : ℝ} (hε : 0 < εaffine) : 0 < twoLevelSlotMesh εaffine := by
  have hμ := geometry_loss_unit_pos 1 εaffine one_pos hε
  exact lt_min (Cycle25.Energy.commonMesh_pos _ 28 1 _ (by norm_num) (by norm_num) (by positivity))
    (by have := secondStepMesh_pos hε; positivity)

theorem twoLevelSlotMesh_le_low (εaffine : ℝ) :
    twoLevelSlotMesh εaffine ≤ Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8) :=
  min_le_left _ _

theorem twoLevelSlotMesh_slot (εaffine : ℝ) : 5/2*twoLevelSlotMesh εaffine ≤ secondStepMesh εaffine := by
  have h := min_le_right (Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8))
    (2/5*secondStepMesh εaffine)
  unfold twoLevelSlotMesh
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
