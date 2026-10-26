/- Repeated marks: the common-width gain payment for the repeated-mark gain.
Fork of the HIGH case of Collet's HighScalar/GainPayment.lean (Apache-2.0). Lemma C
(`gainK_payment`) replaces `High.common_gain_reserve`; its `1/12` slack is not used downstream.
The gain is evaluated at the nonnegative parts of its arguments, so that the payment holds for
arbitrary live widths and frequency caps. -/
import Submissions.arvi_repeated_marks_20261024.Source.PhysicalReserveK
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Source
noncomputable section
open Record1252270103Finite QRH.Record1252270103Source.PhysicalScalar

/-- The repeated-mark gain of a HIGH parent, at the nonnegative parts of the widths. -/
def gainAtK (h : Source) (ν S F : ℝ) : ℝ :=
  QRH.RepeatedMarks.gainK ν 8 (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (max S 0) (max F 0)

/-- The shape of an admissible HIGH parent. -/
def GainParametersK (h : Source) : Prop :=
  (22/23:ℝ)≤h.B ∧ (h.B:ℝ)≤1 ∧ 1<(h.L:ℝ) ∧ 0≤(h.cap:ℝ) ∧ (h.cap:ℝ)≤1

lemma parentParams_of {h : Source} (hp : GainParametersK h) {ν : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) : QRH.RepeatedMarks.ParentParams ν 8 h.B h.L h.cap :=
  ⟨by linarith, hν1, by norm_num, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

lemma gainAtK_of_nonneg (h : Source) (ν : ℝ) {S F : ℝ} (hS : 0≤S) (hF : 0≤F) :
    gainAtK h ν S F=QRH.RepeatedMarks.gainK ν 8 (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) S F := by
  rw [gainAtK, max_eq_left hS, max_eq_left hF]

/-- Lemma C for the clamped gain. -/
lemma gainAtK_payment {h : Source} (hp : GainParametersK h) {ν S F L Q δ : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hS : 0≤S) (h2SF : 2*S≤F) (hδ : 0≤δ)
    (hSL : S≤L+δ) (hFQ : F≤Q+2*δ) :
    gainAtK h ν S F≤gainAtK h ν L Q+ν*δ := by
  have hF : 0≤F := by linarith
  rw [gainAtK_of_nonneg h ν hS hF]
  exact QRH.RepeatedMarks.gainK_payment (parentParams_of hp hν0 hν1) hS h2SF
    (le_max_right L 0) (le_max_right Q 0) hδ
    (hSL.trans (by linarith [le_max_left L 0])) (hFQ.trans (by linarith [le_max_left Q 0]))

lemma gainAtK_homogeneous {h : Source} (hp : GainParametersK h) {ν S F D : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hS : 0≤S) (hF : 0≤F) (hD : 0≤D) :
    gainAtK h ν (D*S) (D*F)=D*gainAtK h ν S F := by
  rw [gainAtK_of_nonneg h ν (mul_nonneg hD hS) (mul_nonneg hD hF), gainAtK_of_nonneg h ν hS hF]
  exact QRH.RepeatedMarks.gainK_smul (parentParams_of hp hν0 hν1) hS hF hD

lemma selectedGainK_eq (n low h : Source) (b ν : ℝ) (hS : 0≤b-2*(n.allowance:ℝ))
    (hF : 0≤sourceFReal n low b-(n.allowance:ℝ)) :
    selectedGainK n low h b ν=
      gainAtK h ν (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ)) := by
  rw [gainAtK_of_nonneg h ν hS hF]
  rfl

/-- The repeated-mark gap pays the first, second and forced common losses. -/
lemma actual_gap_gain_payment_K (n low h : Source) (hp : GainParametersK h)
    (b ν reserve D live frequency c d forced : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD : 0≤D)
    (hc : 0≤c) (hd : 0≤d) (hforced : 0≤forced)
    (hg : ActualGapsK n low h b ν reserve)
    (hslots : D*(b-2*(n.allowance:ℝ))≤live+c+d+forced)
    (hrows : D*(sourceFReal n low b-(n.allowance:ℝ))≤frequency+2*c+2*d) :
    D*(sourceBase n low b ν-1)-ν*(c+d+forced)-gainAtK h ν live frequency≤
      -D*((n.highFee:ℝ)+reserve) := by
  obtain ⟨hgap,-,hS,hcell⟩ := hg
  have hF : 0≤sourceFReal n low b-(n.allowance:ℝ) := by linarith
  have hpay := gainAtK_payment hp (S:=D*(b-2*(n.allowance:ℝ)))
    (F:=D*(sourceFReal n low b-(n.allowance:ℝ))) (L:=live) (Q:=frequency) (δ:=c+d+forced)
    hν0 hν1 (mul_nonneg hD hS) (by nlinarith) (by linarith) (by linarith) (by linarith)
  rw [gainAtK_homogeneous hp hν0 hν1 hS hF hD, ←selectedGainK_eq n low h b ν hS hF] at hpay
  have hg' := mul_le_mul_of_nonneg_left hgap hD
  nlinarith

end
end QRH.RepeatedMarks.Source
