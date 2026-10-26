/- Repeated marks: the NF source step of the repeated-mark graph.
Fork of Collet's `nf_truncated` (Core/InitialRegularCallbacks.lean), `nf_physical_of_truncated`
(Core/InitialTruncatedCallbacks.lean) and `nf_step_of_physical` (Low/HeightAnchorCallbacks.lean),
Apache-2.0, for a node with a HIGH parent: the reserve is the repeated-mark reserve, the widths and
the geometry come from the kept gates, and the HIGH supplier is the repeated-mark supplier. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Low.GlobalInitialCallbacks
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103StepScalar.Geometry
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.Chain
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncated
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularParameters
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialTruncatedCallbacks
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Source
noncomputable section
open OAI.SevenEighths Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103Source QRH.Record1252270103Source.InitialTruncated
open QRH.Record1252270103Source.PhysicalScalar QRH.Record1252270103Source.PhysicalAnalytic
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Source.FixedWidthPhysical
open QRH.Record1252270103Source.InitialRegularToTruncated
open QRH.RepeatedMarks.Finite

private theorem beta_seven_eighths : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  QRH.RepeatedMarks.beta_le_seven_eighths

/-- The truncated supplier on the certified width grid. -/
theorem nf_truncated2 (n low h : Source) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hK : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (hv : SourceValid2 n low (some h))
    (hlow : ParentGood low) (ha : NFAccounting n) (hG : P low) (hGH : P h) :
    ∃loss:ℝ,∀ε:ℝ,0<ε→
      ∀b∈activeWidthGrid (crossing n low) n.cap (nfWidthDelta_rm n low (some h) hv.1 ha loss),
      ∃m x:ℝ,0 < m ∧ 0<x ∧ ∀mesh ξ:ℝ,0 < mesh→mesh ≤ m→0<ξ→ξ≤x→
        FixedSubsetTruncatedSupplier n.B n.L n.cap (crossing n low) QRH.RepeatedMarks.natK
          mesh ξ ε b (nfWidthDelta_rm n low (some h) hv.1 ha loss) := by
  have hn:=QRH.RepeatedMarks.Graph.parent_good_of_valid2 hv
  have hallow:0<(n.allowance:ℝ):=by exact_mod_cast (nf_accounting_positive ha).1
  have hfee0:0≤(n.highFee:ℝ):=by exact_mod_cast (nf_accounting_positive ha).2.2.le
  have fields:=hv.1
  rcases fields with ⟨hBn,hB,hLn,hcap0,hcap1,hq,hq34,_,_,_,_,hshape,_⟩
  have hq0:(1/2:ℝ)≤(n.q:ℝ):=by
    have hh:= (Rat.cast_le (K:=ℝ)).mpr hq
    norm_num at hh
    exact hh
  have hq1:(n.q:ℝ)≤1:=by
    have hh:(n.q:ℝ)≤3/4:=by
      have hh:= (Rat.cast_le (K:=ℝ)).mpr hq34
      norm_num at hh
      exact hh
    linarith
  obtain ⟨reserve,hr,hgapsK⟩:=nf_actual_uniform_reserve_K n low h hv
  obtain ⟨σ,θ,loss,hσ,hσr,hσa,hf,hθstep,hloss,hwidth,hmeshes⟩:=
    regular_meshes_from_sources (9/2) n low (some h) reserve hr hn hlow hallow hq0 hq1 hG
      (by
        intro h' hh'
        simp only [Option.mem_def, Option.some.injEq] at hh'
        subst hh'
        exact hGH)
  refine ⟨loss,?_⟩
  intro ε hε b hb
  let width:=nfWidthDelta_rm n low (some h) hv.1 ha loss
  have hc:=nf_width_certificate_rm n low (some h) hv.1 ha loss
  have hw0:0≤width:=hc.2.1.le
  have hw:=hwidth width hw0 hc.2.2.2.1
  have hbI:=activeWidthGrid_bounds (crossing n low) n.cap width b hb
  have hg:=nf_real_geometry_rm n low (some h) hv.1 hlow hbI
  obtain ⟨m,x,hm,hx,hceil⟩:=hmeshes b hg
  refine ⟨m,x,hm,hx,?_⟩
  intro mesh ξ hm0 hmm hx0 hxx
  obtain ⟨hLowMesh,hParent,hMesh,hAmp,hMeshSmall,hXi,hXiStep,hCard⟩:=hceil mesh ξ hm0 hmm hx0 hxx
  have sc:=scalar_of_regular_mesh _ n low b σ θ mesh ξ width hg hn hlow hallow hf hσa hθstep
    hx0 hXi hm0.le hMeshSmall hw0 hw.1
  have hbcell:b≤1:=hbI.2.trans (by exact_mod_cast hcap1.le)
  have hregular:RegularJointSupplier (9/2) n low b mesh ξ θ width:=by
    obtain ⟨hB0,hB1,hlam,hc0,hc1⟩:=hshape h (by simp)
    exact regular_supplier_some_rm
      (Kgraph:=9/2) (n:=n) (low:=low) (bcell:=b) (reserve:=σ)
      (θ:=θ) (mesh:=mesh) (ξ:=ξ) (width:=width) (hf:=hf) (sc:=sc)
      (hmesh:=hMesh) (hwidth:=hw.1) (hbcell:=hbcell) (hr:=hσa) (hfee:=hfee0)
      (hq:=hq0) (hq1:=hq1) (hG:=hG) (hLowMesh:=hLowMesh) (hβ:=hβ) (hβhi:=beta_seven_eighths)
      hAmp h (by
        have hh:= (Rat.cast_le (K:=ℝ)).mpr hB0
        norm_num at hh
        exact hh) (by exact_mod_cast hB1) (by exact_mod_cast hlam)
      (by exact_mod_cast hc0) (by exact_mod_cast hc1) hParent
      (fun ν hν=>actualGaps_rm_of_K (actualGapsK_mono hσr (hgapsK b hbI ν hν)))
  have hbound:=truncated_of_regular _ n low b mesh ξ θ width ε hg
    (by exact_mod_cast hB) (by exact_mod_cast hLn.le) (by exact_mod_cast hcap1.le)
    (by exact_mod_cast hlow.2.1) hallow hfee0 hm0.le hAmp hx0
    (hXi.trans (hf.small.trans (by norm_num))) hXiStep hf.positive.le
    (hf.small.trans (by norm_num)) hθstep hw.2 hregular
  have hcast:((9/2:ℚ):ℝ)=QRH.RepeatedMarks.natK:=by norm_num [QRH.RepeatedMarks.natK]
  exact Eq.mp (congrArg (fun κ:ℝ=>FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ)
    (n.cap:ℝ) (crossing n low:ℝ) κ mesh ξ ε b width) hcast) hbound

/-- The marked physical supplier on the width cells. -/
theorem nf_physical2 (n low h : Source) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hK : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (hv : SourceValid2 n low (some h))
    (hlow : ParentGood low) (ha : NFAccounting n) (hG : P low) (hGH : P h) :
    ∃loss : ℝ,∀ε : ℝ,0<ε → ∃mesh ξ : ℝ,0 < mesh ∧ 0<ξ ∧
      QRH.Record1252270103Low.HeightAnchor.InitialMarkedPhysicalSupplier n.B n.L n.cap (crossing n low)
        QRH.RepeatedMarks.natK mesh ξ ε
        (nfWidthCell_rm n low (some h) hv.1 ha loss) := by
  obtain ⟨loss,hfixed⟩:=nf_truncated2 n low h hβ hK hv hlow ha hG hGH
  have hc:=nf_width_certificate_rm n low (some h) hv.1 ha loss
  refine ⟨loss,?_⟩
  intro ε hε
  apply physical_supplier_of_truncated_widths n.B n.L n.cap (crossing n low) QRH.RepeatedMarks.natK ε
    (nfWidthDelta_rm n low (some h) hv.1 ha loss) (by exact_mod_cast hv.1.2.1)
    (by exact_mod_cast hv.1.2.2.1.le) (by exact_mod_cast hv.1.2.2.2.2.1.le) hε hc.2.1
  · intro b hb
    have hr:=(hc.2.2.2.2.2.1.radius_pos b (activeWidthGrid_bounds _ _ _ b hb)).le
    have he:=upperWidthCell_fixed_on_grid (crossing n low) n.cap _ b hc.2.1 hb
    simpa only [nfWidthCell_rm,he] using hr
  · exact hfixed ε hε

/-- The NF source step of the repeated-mark graph. -/
theorem nf_step2 : QRH.RepeatedMarks.Graph.NFStep2 := by
  intro n low h hb hK hv hlow ha hp hph
  obtain ⟨loss,hphys⟩:=nf_physical2 n low h hb hK hv hlow ha hp hph
  have hfields:=hv.1
  obtain ⟨hBn,hBn1,hLn,_,_,_,_,hL,_,_,hcrosslow,_⟩:=hfields
  have hn0 : 0≤(n.B:ℝ):=by exact_mod_cast hBn.le
  have hn1 : (n.B:ℝ)≤1:=by exact_mod_cast hBn1
  have hLn' : 1≤(n.L:ℝ):=by exact_mod_cast hLn.le
  have hL' : (n.L:ℝ)≤(low.L:ℝ):=by exact_mod_cast hL.le
  have hcross : (crossing n low:ℝ)≤(low.cap:ℝ):=by exact_mod_cast hcrosslow
  have hbudget : (n.B:ℝ)-(low.B:ℝ)+((low.L:ℝ)-(n.L:ℝ))*(crossing n low:ℝ)≤0:=
    (crossing_real_identity n low hL).le
  have hcells : ReferenceWidthCells (crossing n low) n.cap QRH.RepeatedMarks.natK
      (nfWidthCell_rm n low (some h) hv.1 ha loss):=
    (nf_width_certificate_rm n low (some h) hv.1 ha loss).2.2.2.2.2.1.reference
  change GlobalSource n.B n.L n.cap
  apply globalSource_of_squarefree n.B n.L n.cap hn0 (by linarith)
  apply QRH.Record1252270103Low.HeightAnchor.uniform_squarefree_source_step n.B n.L n.cap low.B
    low.L low.cap (crossing n low)
    QRH.RepeatedMarks.natK (QRH.RepeatedMarks.natK/6) (nfWidthCell_rm n low (some h) hv.1 ha loss) hn0 hn1
    (by exact_mod_cast hlow.2.1) hLn' hL' hcross hbudget
  · norm_num [QRH.RepeatedMarks.natK]
  · norm_num [QRH.RepeatedMarks.natK]
  · linarith only [hK]
  · ring_nf
    exact le_rfl
  · exact hb
  · exact hcells
  · exact hp
  · exact hphys

end
end QRH.RepeatedMarks.Source
