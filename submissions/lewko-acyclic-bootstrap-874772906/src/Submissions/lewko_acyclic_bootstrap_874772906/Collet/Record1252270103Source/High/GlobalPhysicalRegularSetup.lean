/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed width loss and both source meshes precede the original slot type.
The slot-dependent buffer is selected only after its cardinality is known. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalCombinedLosses
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalLowGuardCells
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open Record1252270103Finite Record1252270103StepScalar PhysicalAnalytic

/-- One width-grid loss works before b, mesh, cardinality or source profiles.
The later width certificate supplies the sole scalar `widthPayment`. -/
theorem fixed_regular_setup (n:Source)(reserve:ℝ)
    (hr:0<reserve)(ha:0<(n.allowance:ℝ))(hL:0≤(n.L:ℝ)):
    ∃σ θ outerLoss:ℝ,0<σ ∧ σ≤reserve ∧ σ≤(n.allowance:ℝ) ∧
      FixedBudget σ 100 100 1 θ ∧ 0<outerLoss ∧
      (∀width:ℝ,0≤width→|outerLoss| *width≤(n.allowance:ℝ)→
        width≤θ ∧ width≤PhysicalLowGuard.step n) ∧
      ∀lowMesh highMesh amp:ℝ,0<lowMesh→0<highMesh→0<amp→
      ∃m x:ℝ,0<m ∧ 0<x ∧ ∀mesh ξ:ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        mesh≤lowMesh ∧ 100*mesh≤highMesh ∧ 100*mesh≤θ ∧ mesh<amp/2 ∧
        mesh≤(n.allowance:ℝ)/4 ∧ ξ≤θ ∧ ξ≤PhysicalLowGuard.step n ∧
        ∀N:ℕ,∃wmin rmin εslot:ℝ,CardinalityBudget θ 100 100 1 1 N wmin rmin εslot := by
  let σ:=min reserve (n.allowance:ℝ)
  have hσ:0<σ:=lt_min hr ha
  obtain ⟨θ,hθ⟩:=fixed_loss_exists σ 100 100 1 hσ (by norm_num) (by norm_num) (by norm_num)
  let outerLoss:=max (16*((n.L:ℝ)+1)) ((n.allowance:ℝ)/θ)
  have houter:0<outerLoss:=lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hwidth:∀width:ℝ,0≤width→|outerLoss| *width≤(n.allowance:ℝ)→
      width≤θ ∧ width≤PhysicalLowGuard.step n:=by
    intro width hw hpay
    have hl:16*((n.L:ℝ)+1)≤|outerLoss|:=by
      rw [abs_of_pos houter]
      exact le_max_left _ _
    have hθloss:(n.allowance:ℝ)/θ≤|outerLoss|:=by
      rw [abs_of_pos houter]
      exact le_max_right _ _
    have hproduct:((n.allowance:ℝ)/θ)*width≤(n.allowance:ℝ):=
      (mul_le_mul_of_nonneg_right hθloss hw).trans hpay
    have hscaled:=mul_le_mul_of_nonneg_right hproduct hθ.positive.le
    have heq:((n.allowance:ℝ)/θ)*width*θ=(n.allowance:ℝ)*width:=by
      field_simp [hθ.positive.ne']
    rw [heq] at hscaled
    exact ⟨(by nlinarith only [hscaled,ha]),
      PhysicalLowGuard.width_le_step n outerLoss width hL hw hl hpay⟩
  refine ⟨σ,θ,outerLoss,hσ,min_le_left _ _,min_le_right _ _,hθ,houter,hwidth,?_⟩
  intro lowMesh highMesh amp hlow hhigh hamp
  obtain ⟨m,hm,hmesh⟩:=cell_mesh_ceiling lowMesh highMesh θ amp hlow hhigh hθ.positive hamp
  have hstep:0<PhysicalLowGuard.step n:=by
    unfold PhysicalLowGuard.step
    positivity
  refine ⟨m,min θ (PhysicalLowGuard.step n),hm,lt_min hθ.positive hstep,?_⟩
  intro mesh ξ hm0 hmm hx0 hxx
  have hmes:=hmesh mesh hm0 hmm
  have hma:mesh≤(n.allowance:ℝ)/4:=by
    have hs:σ≤(n.allowance:ℝ):=min_le_right _ _
    nlinarith only [hmes.2.2.1,hθ.tiny,hθ.positive,hs,hm0]
  exact ⟨hmes.1,hmes.2.1,hmes.2.2.1,hmes.2.2.2,hma,
    hxx.trans (min_le_left _ _),hxx.trans (min_le_right _ _),
    fun N=>cardinality_loss_exists θ 100 100 1 1 hθ.positive (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) N⟩

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.fixed_regular_setup
