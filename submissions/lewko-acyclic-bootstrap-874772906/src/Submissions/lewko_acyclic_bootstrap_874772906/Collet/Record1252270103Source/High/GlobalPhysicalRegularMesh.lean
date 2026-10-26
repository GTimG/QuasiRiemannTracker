/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One width-grid loss is fixed before b and all original slot types. Genuine
earlier sources then supply positive per-cell meshes for every smaller mesh. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularLowParameters
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open Record1252270103Finite Record1252270103StepScalar PhysicalAnalytic
open QRH.Record1252270103Graph

theorem regular_meshes_from_sources (K:ℚ)(n low:Source)(high:Option Source)(reserve:ℝ)
    (hr:0<reserve)(hn:ParentGood n)(hlow:ParentGood low)(ha:0<(n.allowance:ℝ))
    (hqhalf:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
    (hGH:∀h∈high,GlobalSource (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)):
    ∃σ θ outerLoss:ℝ,0<σ ∧ σ≤reserve ∧ σ≤(n.allowance:ℝ) ∧
      (∃hf:FixedBudget σ 100 100 1 θ, θ≤PhysicalLowGuard.step n ∧ 0<outerLoss ∧
      (∀width:ℝ,0≤width→|outerLoss| *width≤(n.allowance:ℝ)→
        width≤θ ∧ width≤PhysicalLowGuard.step n) ∧
      ∀b:ℝ,∀hg:RealGeometry K n low b,
      ∃m x:ℝ,0<m ∧ 0<x ∧ ∀mesh ξ:ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        mesh≤regularLowMesh K n low b θ hg hn hlow ha hqhalf hq1 hG
          hf.positive ∧
        (match high with
          | none=>100*mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) θ
          | some h=>QRH.Record12518109Existence.UnitFaceSource
              (globalFace (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)) (100*mesh) θ) ∧
        100*mesh≤θ ∧ mesh<sourceAReal n low b/2 ∧ mesh≤(n.allowance:ℝ)/4 ∧
        ξ≤θ ∧ ξ≤PhysicalLowGuard.step n ∧
        ∀N:ℕ,∃wmin rmin εslot:ℝ,CardinalityBudget θ 100 100 1 1 N wmin rmin εslot):=by
  have hL:0≤(n.L:ℝ):=by exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<1) hn.2.2.1).le
  have hstep:0<PhysicalLowGuard.step n:=by unfold PhysicalLowGuard.step;positivity
  obtain ⟨σ,θ,outerLoss,hσ,hres,hallow,hf,houter,hwidth,hceil⟩:=
    fixed_regular_setup n (min reserve (PhysicalLowGuard.step n)) (lt_min hr hstep) ha hL
  have hθstep:θ≤PhysicalLowGuard.step n:=by
    have hs:=hres.trans (min_le_right _ _)
    linarith only [hf.tiny,hf.positive,hs]
  refine ⟨σ,θ,outerLoss,hσ,hres.trans (min_le_left _ _),hallow,hf,hθstep,houter,hwidth,?_⟩
  intro b hg
  obtain ⟨mh,hmh,hh⟩:=selected_high_parent_mesh high θ hf.positive hGH
  have hml:=regular_low_mesh_positive K n low b θ hg hn hlow ha hqhalf hq1 hG hf.positive
  obtain ⟨m,x,hm,hx,hsmall⟩:=hceil _ mh (sourceAReal n low b) hml hmh hg.a_pos
  refine ⟨m,x,hm,hx,?_⟩
  intro mesh ξ hm0 hmm hx0 hxx
  have hc:=hsmall mesh ξ hm0 hmm hx0 hxx
  exact ⟨hc.1,hh (100*mesh) hc.2.1,hc.2.2⟩
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_meshes_from_sources
