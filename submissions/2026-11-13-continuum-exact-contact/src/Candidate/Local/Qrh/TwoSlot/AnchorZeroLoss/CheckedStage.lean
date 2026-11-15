/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual paired anchor step for every real point of an exactly checked stage. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.CertificateHigh
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.PairedStage

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native

/-- The checked HIGH hypotheses pay tiny cores and every permitted class. -/
theorem class_ledger (s : Stage) (hok : s.ok=true) (r : ℝ)
    (hlo : (s.left:ℝ)≤r) (hhi : r ≤ s.R) :
    High.tinyEx r (fs (s.R:ℝ) s.gain s.cut r) (fH (s.R:ℝ) r)≤fu (s.R:ℝ) r-3/100 ∧
    ∀p∈High.classes (s.cut:ℝ),∃w∈High.cutoffs,(s.R:ℝ)+1/1000000000000≤w ∧
      w+High.sig s.a0 s.a1 w≤6 ∧
      High.detEx s.a0 s.a1 p.1 p.2 w r (fs (s.R:ℝ) s.gain s.cut r) (fH (s.R:ℝ) r)≤fu (s.R:ℝ) r := by
  have hS := ordinary_hyp s hok r hlo hhi
  have hH := high_hyp s hok r hlo hhi
  have er := highData_r s r hS.R_pos.ne'
  have es := highData_s s r hS.R_pos.ne' hS.k_pos.ne'
  have hhalf : 1/2≤(highData s r).H := by
    change (1/2:ℝ)≤fH (s.R:ℝ) r
    linarith [hS.H_ge]
  have hsmall : fs (s.R:ℝ) s.gain s.cut r≤137/1000 := by
    dsimp only [fs]
    linarith [hS.g2,hS.u_nonneg]
  constructor
  · have ht := High.Stg.tiny_le hH
    rw [er,es] at ht
    exact ht
  · intro p hp
    rcases hp with ⟨hp1,hp2,hp3,hp4⟩
    let w := (highData s r).w p.1
    have hw := High.Stg.w_mem hH hp1 hp2
    have hsupply := High.Stg.sig_le_supply hH hp1
    rw [es] at hsupply
    change (highData s r).H*High.sig (s.a0:ℝ) s.a1 w≤fs (s.R:ℝ) s.gain s.cut r at hsupply
    have hsig0 := High.sig_nonneg (s.a0:ℝ) s.a1 w
    have hwmax : w≤79/100 := hw.2
    have hsig : High.sig s.a0 s.a1 w≤2*(137/1000:ℝ) := by
      nlinarith only [hhalf,hsupply,hsig0,hsmall]
    have hd := High.Stg.detEx_le hH hp1 hp2 hp3 hp4
    rw [er,es] at hd
    exact ⟨w,hw,High.Stg.R_le_w hH hp1,by linarith,hd⟩

/-- A kernel-checked stage gives its full actual paired output, once the entry
anchor and the preceding anchors have been supplied by the finite induction. -/
theorem checked_stage_anchor (s : Stage) (hok : s.ok=true) (F : ParentFace)
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hentry : AnchorAt s.R s.gain)
    (hprior : ∀x : ℝ,(s.R:ℝ)<x → x≤311/400 → ∃gain : ℝ,0≤gain ∧
      (s.a0:ℝ)-(s.a1:ℝ)*x≤gain ∧ AnchorAt x gain)
    (r : ℝ) (hlo : (s.left:ℝ)≤r) (hhi : r ≤ s.R) :
    AnchorAt r (fY (s.R:ℝ) s.gain s.cut r) := by
  have hS := ordinary_hyp s hok r hlo hhi
  have hb := (Stage.ok_sound hok).1
  rcases hb with ⟨hR0,hR1,hleft,hlt,hk0,hk1,hz,ha1,ha1hi,huL,hwble,hline,hrest⟩
  have ha : 0≤(s.a1:ℝ) := Rat.cast_nonneg.mpr ha1
  have hahi : (s.a1:ℝ)≤2/5 := by
    have h : (s.a1:ℝ)<((2/5:ℚ):ℝ) := Rat.cast_lt.mpr ha1hi
    norm_num at h; linarith
  have htop : (s.a0:ℝ)-(s.a1:ℝ)*(311/400)≤0 := by
    rcases hline with ⟨ha0,ha1⟩ | ⟨hline,ha1⟩
    · simp only [ha0,ha1,Rat.cast_zero,zero_mul,sub_zero]; exact le_rfl
    · have h : ((s.line (311/400):ℚ):ℝ)<((0:ℚ):ℝ) := Rat.cast_lt.mpr hline
      norm_num only [Stage.line,fline,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] at h
      exact h.le
  obtain ⟨htiny,hclasses⟩ := class_ledger s hok r hlo hhi
  exact paired_anchor_of_earlier F hS hβ hres hparent hentry
    (show (s.R:ℝ)<(s.R:ℝ)+1/1000000000000 by linarith)
    (show 0≤(s.R:ℝ)+1/1000000000000 by linarith [hS.hR.1])
    (by linarith)
    (show (s.R:ℝ)+1/1000000000000≤High.cutHi by unfold High.cutHi; linarith [hS.hR.2])
    (by norm_num) (by norm_num) ha hahi htop hprior htiny hclasses

end Qrh.TwoSlot.AnchorZeroLoss.Certificate
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Certificate.checked_stage_anchor
