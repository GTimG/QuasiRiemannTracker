/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform source assembly from an earlier ordinary G and the literal marked
physical norm. The physical supplier remains the one explicit analytic leaf. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.AnchorUnit
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyParentUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low.Anchor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily
open QRH.Record12518109Existence QRH.Record1252270103Source QRH.Record1252270103Source.Collision
open QRH.Record1252270103Restoration

theorem physical_supplier_mono_mesh {B lam cap cross K mesh mesh' ξ ε : ℝ} {cell : ℝ→ℝ}
    (h : InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell) (hm : mesh'≤mesh) :
    InitialMarkedPhysicalSupplier B lam cap cross K mesh' ξ ε cell := by
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨degree,S,C,hC,hs⟩:=h α rayM H hH W hW hsW bΦ hbΦ η
    η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨degree,S,C,hC,hs.mono ?_⟩
  intro Z hz hZ T θ w v t height hw hwm
  exact hz hZ T θ w v t height hw (fun i=>(hwm i).trans hm)

/-- The mesh is chosen before the ambient finite slot type. All restoration,
orientation, radial, cardinality and reference bounds are proved by the imported
source joins; no target initial energy is supplied as an assumption. -/
theorem uniform_squarefree_source_step
    (B lam cap B₀ lam₀ cap₀ cross K κ : ℝ) (cell : ℝ→ℝ)
    (hB0 : 0≤B) (hB1 : B≤1) (hB₀ : B₀≤1) (hlam : 1≤lam)
    (hL : lam≤lam₀) (hcrosscap : cross≤cap₀)
    (hcrossbudget : B-B₀+(lam₀-lam)*cross≤0)
    (hκlo : 7/10≤κ) (hκhi : κ≤3/4) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ)
    (hK : 6*κ≤K) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hcells : ReferenceWidthCells cross cap K cell)
    (hlow : GlobalSource B₀ lam₀ cap₀)
    (hphysical : ∀ε : ℝ,0<ε → ∃mesh ξ : ℝ,0<mesh ∧ 0<ξ ∧
      InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell) :
    UniformSquarefreeUnitFaceSource B lam cap := by
  apply uniform_projected_source_lift
  intro ε hε
  obtain ⟨m₀,hm₀,h₀⟩:=hlow (ε/2) (by linarith)
  obtain ⟨mp,ξ,hmp,hξ,hp⟩:=hphysical ε hε
  let mr:=Cycle61FirstActual.comparisonMesh 1 1 (ε/2)
  have hmr : 0<mr:=Cycle61FirstActual.comparisonMesh_pos 1 1 (ε/2) (by norm_num) le_rfl (by linarith)
  let mesh:=min m₀ (min mp mr)
  have hm : 0<mesh:=lt_min hm₀ (lt_min hmp hmr)
  have hm0 : mesh≤m₀:=min_le_left _ _
  have hmp' : mesh≤mp:=(min_le_right _ _).trans (min_le_left _ _)
  have hmr' : mesh≤mr:=(min_le_right _ _).trans (min_le_right _ _)
  have hlow' : ProjectedUnitFaceSource (globalFace B₀ lam₀ cap₀) mesh ε := by
    have hh:=unit_projected_of_ordinary B₀ lam₀ cap₀ mesh (ε/2) (ε/4) hB₀
      (by linarith) (by linarith) (h₀.mono_mesh hm0)
    convert hh using 1 <;> ring
  exact ⟨mesh,hm,projected_unit_source_step B lam cap B₀ lam₀ cap₀ cross K κ mesh ξ ε cell
    hB0 hB1 hlam hξ hε hL hcrosscap hcrossbudget hκlo hκhi hκbeta hK hbeta hmr'
    hcells (physical_supplier_mono_mesh hp hmp') hlow'⟩

end
end QRH.Record1252270103Low.Anchor
#print axioms QRH.Record1252270103Low.Anchor.physical_supplier_mono_mesh
#print axioms QRH.Record1252270103Low.Anchor.uniform_squarefree_source_step
