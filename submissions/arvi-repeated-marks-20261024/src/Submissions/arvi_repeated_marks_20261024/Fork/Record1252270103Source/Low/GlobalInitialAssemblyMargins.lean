/- Repeated marks: fork of Record1252270103Source.Low.GlobalInitialAssemblyMargins (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyMargins
import Submissions.arvi_repeated_marks_20261024.Source.GainC
import Submissions.arvi_repeated_marks_20261024.Source.CountWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.GainPaymentK
import Submissions.arvi_repeated_marks_20261024.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite width cells selected from the checked scalar slack and source fee. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph QRH.Record1252270103StepScalar

theorem nf_finite_width_cells_rm (n low : Source) (high : Option Source)
    (hv : QRH.RepeatedMarks.Finite.SourceValidC n low high) (ha : NFAccounting n) (loss : ℝ) :
    ∃margin δ : ℝ,0<margin ∧ 0<δ ∧ δ≤1 ∧
      |loss| *δ≤(n.allowance:ℝ) ∧ 2*(|loss| *δ)≤margin ∧
      FiniteReferenceCells (crossing n low) n.cap (11243277/2500000) δ
        (upperWidthCell (crossing n low) n.cap δ) ∧
      ∀s∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),∀ν∈Set.Icc (n.q:ℝ) (3/4),
        (∀j,margin/2≤sourceScalarReal (11243277/2500000) n low
          (upperWidthCell (crossing n low) n.cap δ s) j-|loss| *δ) ∧
        0≤sourceWeakReal n low (upperWidthCell (crossing n low) n.cap δ s) ∧
        ∀j,QRH.RepeatedMarks.Finite.KeptGate high j →margin/2≤sourceDensityWidthReal n low high
          (upperWidthCell (crossing n low) n.cap δ s) ν j-|loss| *δ := by
  obtain ⟨margin,hm,hg⟩:=QRH.RepeatedMarks.Finite.nfC_uniform_margin n low high hv
  have ha' : 0<(n.allowance:ℝ) := by exact_mod_cast (nf_accounting_positive ha).1
  let δ:=widthRoundingScale margin n.allowance loss
  obtain ⟨hδ,hδ1,hfee,hslack⟩:=widthRoundingScale_spec margin n.allowance loss hm ha'
  have hν : (n.q:ℝ)∈Set.Icc (n.q:ℝ) (3/4) := ⟨le_rfl,by
    have hh : (n.q:ℝ)≤((3/4:ℚ):ℝ):=Rat.cast_le.mpr hv.2.2.2.2.2.2.1
    norm_num at hh ⊢
    exact hh⟩
  have hcells : FiniteReferenceCells (crossing n low) n.cap (11243277/2500000) δ
      (upperWidthCell (crossing n low) n.cap δ) := by
    apply finite_reference_cells_from_margin _ _ _ margin δ hm hδ
    intro b hb
    simpa [sourceScalarReal] using (hg b hb _ hν).1 (9:Fin 16)
  refine ⟨margin,δ,hm,hδ,hδ1,hfee,hslack,hcells,?_⟩
  intro s hs ν hν'
  have hb:=hcells.bounds s hs
  obtain ⟨hg',hw,hd⟩:=hg _ ⟨hs.1.trans hb.1,hb.2.1⟩ ν hν'
  exact ⟨fun j=>by linarith [hg' j],hw,fun j hj=>by linarith [hd j hj]⟩

end
end QRH.Record1252270103Low
