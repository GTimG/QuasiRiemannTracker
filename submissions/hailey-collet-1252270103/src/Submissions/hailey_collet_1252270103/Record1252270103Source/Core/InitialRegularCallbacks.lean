/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncated
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularParameters
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialTruncatedCallbacks
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.Incumbent
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI.SevenEighths Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph QRH.Record1252270103Low
open InitialTruncated PhysicalScalar PhysicalAnalytic High.GlobalPhysical FixedWidthPhysical

private theorem beta_seven_eighths : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  QRH.Record1252270103Bootstrap.incumbent_beta.trans (by norm_num)

theorem seed_truncated : SeedTruncatedInlet := by
  intro n low hβ hK hv hlow hG
  have hn:=parent_good_of_seed_valid hv
  have ha:=PhysicalLowGuard.seed_allowance_positive n low hv
  have fields:=hv
  rcases fields with ⟨hBn,hB,hLn,hcap0,hcap1,hq,hq34,_,_,_,_,_,_,hfee,_⟩
  have hq0:(1/2:ℝ)≤(n.q:ℝ):=by
    have h:= (Rat.cast_le (K:=ℝ)).mpr hq
    norm_num at h
    exact h
  have hq1:(n.q:ℝ)≤1:=by
    have h:(n.q:ℝ)<3/4:=by
      have h:= (Rat.cast_lt (K:=ℝ)).mpr hq34
      norm_num at h
      exact h
    linarith
  have hfee0:0≤(n.highFee:ℝ):=by rw [hfee];norm_num
  obtain ⟨reserve,hr,hgaps⟩:=seed_actual_uniform_reserve n low hv
  obtain ⟨σ,θ,loss,hσ,hσr,hσa,hf,hθstep,hloss,hwidth,hmeshes⟩:=
    regular_meshes_from_sources (112445673/25000000) n low none reserve hr hn hlow ha hq0 hq1 hG
      (by simp)
  refine ⟨loss,?_⟩
  intro ε hε b hb
  let width:=seedWidthDelta n low hv loss
  have hc:=seed_width_certificate n low hv loss
  have hw0:0≤width:=hc.2.1.le
  have hw:=hwidth width hw0 hc.2.2.2.1
  have hbI:=activeWidthGrid_bounds (crossing n low) n.cap width b hb
  have hg:=seed_real_geometry n low hv hlow hbI
  obtain ⟨m,x,hm,hx,hceil⟩:=hmeshes b hg
  refine ⟨m,x,hm,hx,?_⟩
  intro mesh ξ hm0 hmm hx0 hxx
  obtain ⟨hLowMesh,hParent,hMesh,hAmp,hMeshSmall,hXi,hXiStep,hCard⟩:=hceil mesh ξ hm0 hmm hx0 hxx
  have sc:=scalar_of_regular_mesh _ n low b σ θ mesh ξ width hg hn hlow ha hf hσa hθstep
    hx0 hXi hm0.le hMeshSmall hw0 hw.1
  have hbcell:b≤1:=hbI.2.trans (by exact_mod_cast hcap1.le)
  have hregular:=regular_supplier_natural
    (Kgraph:=112445673/25000000) (n:=n) (low:=low) (bcell:=b) (reserve:=σ)
    (θ:=θ) (mesh:=mesh) (ξ:=ξ) (width:=width) (hf:=hf) (sc:=sc)
    (hmesh:=hMesh) (hwidth:=hw.1) (hbcell:=hbcell) (hr:=hσa) (hfee:=hfee0)
    (hq:=hq0) (hq1:=hq1) (hG:=hG) (hLowMesh:=hLowMesh) (hβ:=hβ) (hβhi:=beta_seven_eighths)
    hAmp hParent (fun ν hν=>actual_gaps_mono hσr (hgaps b hbI ν hν))
  have hbound:=truncated_of_regular _ n low b mesh ξ θ width ε hg
    (by exact_mod_cast hB) (by exact_mod_cast hLn.le) (by exact_mod_cast hcap1.le)
    (by exact_mod_cast hlow.2.1) ha hfee0 hm0.le hAmp hx0
    (hXi.trans (hf.small.trans (by norm_num))) hXiStep hf.positive.le
    (hf.small.trans (by norm_num)) hθstep hw.2 hregular
  have hcast:((112445673/25000000:ℚ):ℝ)=seedK:=by norm_num [seedK]
  exact Eq.mp (congrArg (fun κ:ℝ=>FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ)
    (n.cap:ℝ) (crossing n low:ℝ) κ mesh ξ ε b width) hcast) hbound

theorem nf_truncated : NFTruncatedInlet := by
  intro n low high hβ hK hv hlow ha hG hGH
  have hn:=parent_good_of_source_valid hv
  have hallow:0<(n.allowance:ℝ):=by exact_mod_cast (nf_accounting_positive ha).1
  have hfee0:0≤(n.highFee:ℝ):=by exact_mod_cast (nf_accounting_positive ha).2.2.le
  have fields:=hv
  rcases fields with ⟨hBn,hB,hLn,hcap0,hcap1,hq,hq34,_,_,_,_,hshape,_⟩
  have hq0:(1/2:ℝ)≤(n.q:ℝ):=by
    have h:= (Rat.cast_le (K:=ℝ)).mpr hq
    norm_num at h
    exact h
  have hq1:(n.q:ℝ)≤1:=by
    have h:(n.q:ℝ)≤3/4:=by
      have h:= (Rat.cast_le (K:=ℝ)).mpr hq34
      norm_num at h
      exact h
    linarith
  obtain ⟨reserve,hr,hgaps⟩:=nf_actual_uniform_reserve n low high hv
  obtain ⟨σ,θ,loss,hσ,hσr,hσa,hf,hθstep,hloss,hwidth,hmeshes⟩:=
    regular_meshes_from_sources (11243277/2500000) n low high reserve hr hn hlow hallow hq0 hq1 hG hGH
  refine ⟨loss,?_⟩
  intro ε hε b hb
  let width:=nfWidthDelta n low high hv ha loss
  have hc:=nf_width_certificate n low high hv ha loss
  have hw0:0≤width:=hc.2.1.le
  have hw:=hwidth width hw0 hc.2.2.2.1
  have hbI:=activeWidthGrid_bounds (crossing n low) n.cap width b hb
  have hg:=nf_real_geometry n low high hv hlow hbI
  obtain ⟨m,x,hm,hx,hceil⟩:=hmeshes b hg
  refine ⟨m,x,hm,hx,?_⟩
  intro mesh ξ hm0 hmm hx0 hxx
  obtain ⟨hLowMesh,hParent,hMesh,hAmp,hMeshSmall,hXi,hXiStep,hCard⟩:=hceil mesh ξ hm0 hmm hx0 hxx
  have sc:=scalar_of_regular_mesh _ n low b σ θ mesh ξ width hg hn hlow hallow hf hσa hθstep
    hx0 hXi hm0.le hMeshSmall hw0 hw.1
  have hbcell:b≤1:=hbI.2.trans (by exact_mod_cast hcap1.le)
  have hregular:RegularJointSupplier (11243277/2500000) n low b mesh ξ θ width:=by
    cases high with
    | none =>
      exact regular_supplier_natural
        (Kgraph:=11243277/2500000) (n:=n) (low:=low) (bcell:=b) (reserve:=σ)
        (θ:=θ) (mesh:=mesh) (ξ:=ξ) (width:=width) (hf:=hf) (sc:=sc)
        (hmesh:=hMesh) (hwidth:=hw.1) (hbcell:=hbcell) (hr:=hσa) (hfee:=hfee0)
        (hq:=hq0) (hq1:=hq1) (hG:=hG) (hLowMesh:=hLowMesh) (hβ:=hβ) (hβhi:=beta_seven_eighths)
        hAmp hParent (fun ν hν=>actual_gaps_mono hσr (hgaps b hbI ν hν))
    | some high =>
      obtain ⟨hB0,hB1,hlam,hc0,hc1⟩:=hshape high (by simp)
      exact regular_supplier_some
        (Kgraph:=11243277/2500000) (n:=n) (low:=low) (bcell:=b) (reserve:=σ)
        (θ:=θ) (mesh:=mesh) (ξ:=ξ) (width:=width) (hf:=hf) (sc:=sc)
        (hmesh:=hMesh) (hwidth:=hw.1) (hbcell:=hbcell) (hr:=hσa) (hfee:=hfee0)
        (hq:=hq0) (hq1:=hq1) (hG:=hG) (hLowMesh:=hLowMesh) (hβ:=hβ) (hβhi:=beta_seven_eighths)
        hAmp high (by
          have h:= (Rat.cast_le (K:=ℝ)).mpr hB0
          norm_num at h
          exact h) (by exact_mod_cast hB1) (by exact_mod_cast hlam)
        (by exact_mod_cast hc0) (by exact_mod_cast hc1) hParent
        (fun ν hν=>actual_gaps_mono hσr (hgaps b hbI ν hν))
  have hbound:=truncated_of_regular _ n low b mesh ξ θ width ε hg
    (by exact_mod_cast hB) (by exact_mod_cast hLn.le) (by exact_mod_cast hcap1.le)
    (by exact_mod_cast hlow.2.1) hallow hfee0 hm0.le hAmp hx0
    (hXi.trans (hf.small.trans (by norm_num))) hXiStep hf.positive.le
    (hf.small.trans (by norm_num)) hθstep hw.2 hregular
  have hcast:((11243277/2500000:ℚ):ℝ)=finalK:=by norm_num [finalK]
  exact Eq.mp (congrArg (fun κ:ℝ=>FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ)
    (n.cap:ℝ) (crossing n low:ℝ) κ mesh ξ ε b width) hcast) hbound

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.seed_truncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.nf_truncated
