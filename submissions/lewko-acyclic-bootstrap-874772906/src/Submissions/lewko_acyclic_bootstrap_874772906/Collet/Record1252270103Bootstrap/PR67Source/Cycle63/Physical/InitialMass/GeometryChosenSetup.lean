import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryChosenAffine
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMeshChoice
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondStepMesh
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 80000
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass Cycle63MarkedPlain

/-- This cap depends only on the outer error, before any dictionary is chosen. -/
def geometryChosenMesh (ε : ℝ) : ℝ :=
  markedGeometryMesh (min (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
    (Cycle63FirstActual.comparisonMesh 1 1 (ε/2))) (twoLevelSlotMesh (ε/4)))

theorem geometry_chosen_mesh_admission (ε : ℝ) (hε : 0<ε) :
    let μ:=geometryLossUnit 1 (ε/4)
    0<geometryChosenMesh ε ∧
    geometryChosenMesh ε≤Cycle63FirstActual.comparisonMesh 1 1 (ε/2) ∧
    geometryChosenMesh ε≤Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
    geometryChosenMesh ε≤μ/8 ∧
    geometryChosenMesh ε<Cycle63.Arithmetic.amplifierFloor/2 := by
  intro μ
  have ha:=geometry_analytic_mesh_admission 1 1 (ε/4) 2 28 1
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
  have hc:=Cycle63FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) (by norm_num) (by positivity)
  have hle : geometryChosenMesh ε≤geometryAnalyticMesh 1 1 (ε/4) 2 28 1 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hnew := marked_geometry_mesh_gates
    (min (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
      (Cycle63FirstActual.comparisonMesh 1 1 (ε/2))) (twoLevelSlotMesh (ε/4)))
    (lt_min (lt_min ha.1 hc) (twoLevelSlotMesh_pos (by positivity)))
  refine ⟨hnew.1,hnew.2.1.trans ((min_le_left _ _).trans (min_le_right _ _)),hle.trans ha.2.2.1,
    hle.trans ha.2.2.2.1,?_⟩
  change geometryChosenMesh ε<Cycle63.AffineLedger.amplifierFloor/2
  simpa only [one_mul] using hle.trans_lt ha.2.2.2.2

/-- The chosen mesh is admitted by the second step of the two-level ledger: it is at most the common mesh of the width
cap `101/100` of row 5 and `2/5` of the mesh of the second step, at the affine loss `ε/4` of the first step. -/
theorem geometry_chosen_mesh_two_level (ε : ℝ) :
    geometryChosenMesh ε≤Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 (ε/4)/8) ∧
      5/2*geometryChosenMesh ε ≤ secondStepMesh (ε/4) := by
  have h : geometryChosenMesh ε≤twoLevelSlotMesh (ε/4) := (min_le_left _ _).trans (min_le_right _ _)
  have h2 := twoLevelSlotMesh_slot (ε/4)
  exact ⟨h.trans (twoLevelSlotMesh_le_low _),by linarith⟩

/-- The marked cap is fixed before the chosen dictionary. -/
theorem geometry_chosen_marked_mesh (ε : ℝ) :
    geometryChosenMesh ε≤ markedRawMesh*markedCoreMin := by
  have hc : geometryChosenMesh ε≤ markedRawMesh*markedCoreMin/64 := min_le_right _ _
  have hp : 0≤ markedRawMesh*markedCoreMin := mul_nonneg marked_raw_mesh_gates.1.le
    markedCoreMin_pos.le
  nlinarith

/-- Fix the loss and mesh before the chosen dictionary; enlarge only the
radial support bound to meet the high-family admission gate. No analytic
moment estimate is assumed or asserted here. -/
theorem exists_chosen_geometry_setup
    (hgap : Arithmetic.theta<HeckeZeroSupremum.beta) :
    ∃ ε : ℝ,0<ε ∧ ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 ∧
    ∃ A : ChosenData,A.P.mesh≤geometryChosenMesh ε ∧
    ∃ bΦ : ℝ,2≤bΦ ∧ Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ := by
  let ε:=(HeckeZeroSupremum.beta-Arithmetic.theta)/20000
  have hε : 0<ε := by dsimp [ε];positivity
  have hεgap : ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 := by
    dsimp [ε];linarith
  obtain ⟨A,hA⟩:=exists_chosen_data_with_mesh hgap
    (geometry_chosen_mesh_admission ε hε).1
  obtain ⟨b,hb,hs⟩:=CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  refine ⟨ε,hε,hεgap,A,hA,max 2 b,le_max_left _ _,?_⟩
  intro x hx
  exact (show x≤b from hs hx).trans (le_max_right _ _)

/-- A uniform source geometry estimate supplies the genuine chosen affine
input, with the mesh fixed before the dictionary and the support bound fixed
before its analytic height. The source estimate remains explicit here. -/
theorem chosen_affine_of_source_geometry
    (hsource : ∀{D : WeightedQRH.MomentData}
      (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
      (εaffine mesh bΦ : ℝ),0<εaffine →
      mesh < Cycle63.Arithmetic.amplifierFloor/2 → 0 ≤ mesh →
      mesh ≤ geometryLossUnit 1 εaffine/8 →
      mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8) →
      mesh≤ markedRawMesh*markedCoreMin →
      mesh≤Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8) →
      5/2*mesh ≤ secondStepMesh εaffine →
      2≤bΦ → 51/100≤HeckeZeroSupremum.beta → HeckeZeroSupremum.beta≤7/8 →
      ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
        SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ
          (geometryLossUnit 1 εaffine/64)) : ChosenAffineInput := by
  intro hgap
  obtain ⟨ε,hε,hεgap,A,hA,bΦ,hbΦ,hsΦ⟩:=exists_chosen_geometry_setup hgap
  have hm:=geometry_chosen_mesh_admission ε hε
  obtain ⟨τ,hτ,_hτcap,hbudget⟩:=hsource A.F (ε/4) A.P.mesh bΦ (by positivity)
    (hA.trans_lt hm.2.2.2.2) A.P.mesh_pos.le
    (hA.trans hm.2.2.2.1) (hA.trans hm.2.2.1) (hA.trans (geometry_chosen_marked_mesh ε))
    (hA.trans (geometry_chosen_mesh_two_level ε).1)
    ((mul_le_mul_of_nonneg_left hA (by norm_num)).trans (geometry_chosen_mesh_two_level ε).2) hbΦ
    (moment_parameter_gates hgap).2.2 baseline_beta
  refine ⟨A,actual_affine_input_of_geometry A bΦ ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hε hτ ?_ hεgap hsΦ (hA.trans hm.2.1) hbudget⟩
  exact div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) (by positivity))
    (by norm_num)

end
end Cycle63.FinalAssembly

end Record1252270103Bootstrap.PR67
