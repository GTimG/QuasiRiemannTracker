/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryMeshChoice
import Candidate.Cycle62.Physical.InitialMass.GeometryHighLossChoice

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section

/-- Both comparison losses are fixed before constructing the slot dictionary. -/
def geometryFinalMesh (ε Mcap Bmask L : ℝ) : ℝ :=
  min (geometryAnalyticMesh 1 1 (ε/4) Mcap Bmask L)
    (Cycle62FirstActual.comparisonMesh 1 1 (ε/2))

theorem geometry_final_mesh_gates (ε Mcap Bmask L : ℝ)
    (hε : 0<ε) (hcap : 0<Mcap) (hmask : 0≤Bmask) :
    0<geometryFinalMesh ε Mcap Bmask L ∧
    ∀mesh : ℝ,mesh≤geometryFinalMesh ε Mcap Bmask L →
      mesh≤Cycle62FirstActual.comparisonMesh 1 1 (ε/2) ∧
      mesh≤Cycle62FirstActual.comparisonMesh 1 1 (ε/4) ∧
      mesh≤Cycle25.Energy.commonMesh Mcap Bmask L (geometryLossUnit 1 (ε/4)/8) ∧
      mesh≤geometryLossUnit 1 (ε/4)/8 ∧
      mesh<(902420521/120632400000:ℝ)/2 := by
  have hg:=geometry_analytic_mesh_admission 1 1 (ε/4) Mcap Bmask L
    (by norm_num) le_rfl (by positivity) hcap hmask
  have hc:=Cycle62FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) le_rfl (by positivity)
  refine ⟨lt_min hg.1 hc,?_⟩
  intro mesh hm
  have ha : mesh≤geometryAnalyticMesh 1 1 (ε/4) Mcap Bmask L :=
    hm.trans (min_le_left _ _)
  refine ⟨hm.trans (min_le_right _ _),ha.trans hg.2.1,
    ha.trans hg.2.2.1,ha.trans hg.2.2.2.1,?_⟩
  simpa only [one_mul] using ha.trans_lt hg.2.2.2.2

/-- The density degree is known before choosing one common height cutoff.
The same cutoff pays both frequency gates and the density polynomial. -/
def geometryFinalHeight (μ d vslot vplain : ℝ) (J : ℕ) : ℝ :=
  min (μ/(16*((J:ℝ)+1))) (min (d*vslot/8) (d*vplain/16))/2

theorem geometry_final_height_gates (μ d vslot vplain : ℝ) (J : ℕ)
    (hμ : 0<μ) (hd : 0<d) (hs : 0<vslot) (hp : 0<vplain) :
    let τ:=geometryFinalHeight μ d vslot vplain J
    0<τ ∧ τ≤μ/16 ∧ 8*τ≤d*vslot ∧ 16*τ≤d*vplain ∧
      2*τ*((J:ℝ)+1)≤μ/8 := by
  intro τ
  have ht : 0<τ := by dsimp [τ,geometryFinalHeight];positivity
  have hleft : 2*τ≤μ/(16*((J:ℝ)+1)) := by
    dsimp [τ,geometryFinalHeight]
    linarith [min_le_left (μ/(16*((J:ℝ)+1))) (min (d*vslot/8) (d*vplain/16))]
  have hright : 2*τ≤min (d*vslot/8) (d*vplain/16) := by
    dsimp [τ,geometryFinalHeight]
    linarith [min_le_right (μ/(16*((J:ℝ)+1))) (min (d*vslot/8) (d*vplain/16))]
  have hbase:=geometry_high_density_height_choice μ J hμ
  have hτ : τ≤μ/(16*((J:ℝ)+1)) := by linarith
  refine ⟨ht,hτ.trans hbase.2.1,?_,?_,?_⟩
  · have hh:=hright.trans (min_le_left _ _)
    linarith
  · have hh:=hright.trans (min_le_right _ _)
    linarith
  · have hh:=mul_le_mul_of_nonneg_right hτ (show 0≤(J:ℝ)+1 by positivity)
    linarith [hbase.2.2]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_final_mesh_gates
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_final_height_gates
