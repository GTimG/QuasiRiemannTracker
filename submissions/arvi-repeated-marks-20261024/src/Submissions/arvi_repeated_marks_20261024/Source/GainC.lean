/- Repeated marks: the repeated-mark gain in the conventions of Collet's HIGH gain.
Collet's HIGH gain (High/Selection.lean, Apache-2.0) is a minimum of six affine branches, defined
for all real arguments. The repeated-mark gain `G_8` (Gain/Gain.lean) is an infimum over amplitude
classes and is used at nonnegative widths. `gainC` evaluates `G_8` at the nonnegative parts of the
widths inside the parent range, and is `0` outside it. With this convention the statements of
Collet's gain lemmas (High/CommonGain.lean, GainBounds.lean, Rescale.lean, MaxProducts.lean) hold
verbatim, so the mechanically forked modules use them unchanged. Collet's branch identities
`gain_le_branch` and `gain_eq_some_branch` have no counterpart: the lemmas below are proved from
the class-infimum properties of `G_8` instead. -/
import Submissions.arvi_repeated_marks_20261024.Gain.Gain
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GainBounds
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace QRH.RepeatedMarks
noncomputable section

/-- Monotonicity in the slot width `S` (every facet has a nonnegative `S`-coefficient). -/
theorem gainK_mono_S {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S L Q : ℝ}
    (hS : 0 ≤ S) (hSL : S ≤ L) (hQ : 0 ≤ Q) :
    gainK ν K B lam h S Q ≤ gainK ν K B lam h L Q := by
  have hL : 0 ≤ L := hS.trans hSL
  have hne : ((fun p => gainP ν p K B lam h L Q) '' classes).Nonempty :=
    ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  show gainK ν K B lam h S Q ≤ sInf ((fun p => gainP ν p K B lam h L Q) '' classes)
  apply le_csInf hne
  rintro _ ⟨p, hp, rfl⟩
  apply (gainK_le_gainP P hS hQ hp).trans
  show gainP ν p K B lam h S Q ≤ gainP ν p K B lam h L Q
  rw [gainP_eq_inf ν p K B lam h S Q P.hν0.le, gainP_eq_inf ν p K B lam h L Q P.hν0.le]
  apply Finset.le_inf'
  intro k _
  apply (Finset.inf'_le _ (Finset.mem_univ k)).trans
  rw [facetVal_linear ν p K B lam h S Q k, facetVal_linear ν p K B lam h L Q k]
  have hc := facet_coeffs (P.at hp) k
  nlinarith [mul_le_mul_of_nonneg_right hSL hc.1]

end
end QRH.RepeatedMarks

namespace QRH.RepeatedMarks.Source
noncomputable section

open Classical in
/-- The repeated-mark gain (eight copies) at the nonnegative parts of the widths, `0` outside the
parent range. -/
def gainC (ν B lam h S Q : ℝ) : ℝ :=
  if QRH.RepeatedMarks.ParentParams ν 8 B lam h then
    QRH.RepeatedMarks.gainK ν 8 B lam h (max S 0) (max Q 0) else 0

lemma gainC_of {ν B lam h : ℝ} (P : QRH.RepeatedMarks.ParentParams ν 8 B lam h) (S Q : ℝ) :
    gainC ν B lam h S Q=QRH.RepeatedMarks.gainK ν 8 B lam h (max S 0) (max Q 0) := by
  simp only [gainC, P, ite_true]

lemma gainC_of_not {ν B lam h : ℝ} (P : ¬QRH.RepeatedMarks.ParentParams ν 8 B lam h) (S Q : ℝ) :
    gainC ν B lam h S Q=0 := by
  simp only [gainC, P, ite_false]

lemma gainC_eq {ν B lam h S Q : ℝ} (P : QRH.RepeatedMarks.ParentParams ν 8 B lam h)
    (hS : 0≤S) (hQ : 0≤Q) : gainC ν B lam h S Q=QRH.RepeatedMarks.gainK ν 8 B lam h S Q := by
  rw [gainC_of P, max_eq_left hS, max_eq_left hQ]

lemma gainC_nonneg (ν B lam h S Q : ℝ) : 0≤gainC ν B lam h S Q := by
  by_cases P : QRH.RepeatedMarks.ParentParams ν 8 B lam h
  · rw [gainC_of P]
    exact QRH.RepeatedMarks.gainK_nonneg P (le_max_right S 0) (le_max_right Q 0)
  · rw [gainC_of_not P]

/-- The parent range of Collet's gain lemmas. -/
lemma params_of {ν B lam h : ℝ} (hn0 : 1/2≤ν) (hn1 : ν≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) : QRH.RepeatedMarks.ParentParams ν 8 B lam h :=
  ⟨by linarith, hn1, by norm_num, hB0, hB1, hl, hh0, hh1⟩

lemma cmax_eq (ν : ℝ) :
    QRH.Record1252270103Source.High.cmax ν=ν*(1-QRH.RepeatedMarks.baseXi ν) := by
  simp only [QRH.Record1252270103Source.High.cmax, QRH.Record1252270103Source.High.baseXi,
    QRH.Record1252270103Source.High.densityDenom, QRH.RepeatedMarks.baseXi,
    QRH.RepeatedMarks.densityDenom]

lemma cmax_nonneg {ν : ℝ} (hn0 : 1/2≤ν) (hn1 : ν≤3/4) :
    0≤QRH.Record1252270103Source.High.cmax ν := by
  rw [cmax_eq]
  have hd : 0<15-6*ν := by linarith
  have hx : QRH.RepeatedMarks.baseXi ν≤1 := by
    simp only [QRH.RepeatedMarks.baseXi, QRH.RepeatedMarks.densityDenom]
    rw [div_le_one hd]
    linarith
  exact mul_nonneg (by linarith) (by linarith)

lemma sub_max_zero_mono {S L : ℝ} (h : S≤L) : S-max S 0≤L-max L 0 := by
  rcases le_total S 0 with h0 | h0
  · rw [max_eq_right h0]
    rcases le_total L 0 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; linarith
  · rw [max_eq_left h0, max_eq_left (h0.trans h)]; linarith

end
end QRH.RepeatedMarks.Source

namespace QRH.Record1252270103Source.High
noncomputable section
open QRH.RepeatedMarks.Source

/-- Collet's `gain_mono` for the repeated-mark gain. -/
theorem gain_mono_rm {nu B lam h S L Q F : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hSL : S≤L) (hQF : Q≤F) :
    gainC nu B lam h S Q≤gainC nu B lam h L F := by
  have P := params_of hn0 hn1 hB0 hB1 hl hh0 hh1
  rw [gainC_of P, gainC_of P]
  exact (QRH.RepeatedMarks.gainK_mono_S P (le_max_right S 0) (max_le_max hSL le_rfl)
    (le_max_right Q 0)).trans
    (QRH.RepeatedMarks.gainK_mono_Q P (le_max_right L 0) (le_max_right Q 0) (max_le_max hQF le_rfl))

/-- Collet's `gain_le_cmax` for the repeated-mark gain. -/
theorem gain_le_cmax_rm {nu B lam h S Q : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hQ : 0≤Q) :
    gainC nu B lam h S Q≤cmax nu*Q := by
  have P := params_of hn0 hn1 hB0 hB1 hl hh0 hh1
  rw [gainC_of P, max_eq_left hQ, cmax_eq]
  exact QRH.RepeatedMarks.gainK_le_cmax P (le_max_right S 0) hQ

/-- Collet's `gain_row_loss` for the repeated-mark gain. -/
theorem gain_row_loss_rm {nu B lam h S q F : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hq : q≤F) :
    gainC nu B lam h S F≤gainC nu B lam h S q+cmax nu*(F-q) := by
  have P := params_of hn0 hn1 hB0 hB1 hl hh0 hh1
  have hc := cmax_nonneg hn0 hn1
  rw [gainC_of P, gainC_of P]
  have hr := QRH.RepeatedMarks.gainK_row_loss P (le_max_right S 0) (le_max_right q 0)
    (max_le_max hq le_rfl)
  rw [←cmax_eq] at hr
  have hd : max F 0-max q 0≤F-q := by
    rcases le_total q 0 with h1 | h1
    · rw [max_eq_right h1]
      rcases le_total F 0 with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith
    · rw [max_eq_left h1, max_eq_left (h1.trans hq)]
  nlinarith [mul_le_mul_of_nonneg_left hd hc]

/-- Collet's `gain_homogeneous` for the repeated-mark gain. -/
theorem gain_homogeneous_rm {nu B lam h S Q a : ℝ} (hnu : 0≤nu) (ha : 0≤a) :
    gainC nu B lam h (a*S) (a*Q)=a*gainC nu B lam h S Q := by
  by_cases P : QRH.RepeatedMarks.ParentParams nu 8 B lam h
  · rw [gainC_of P, gainC_of P]
    have e1 : max (a*S) 0=a*max S 0 := by rw [mul_max_of_nonneg _ _ ha, mul_zero]
    have e2 : max (a*Q) 0=a*max Q 0 := by rw [mul_max_of_nonneg _ _ ha, mul_zero]
    rw [e1, e2]
    exact QRH.RepeatedMarks.gainK_smul P (le_max_right S 0) (le_max_right Q 0) ha
  · rw [gainC_of_not P, gainC_of_not P, mul_zero]

/-- Collet's `gain_rescale` for the repeated-mark gain. -/
theorem gain_rescale_rm {nu B lam h S F : ℝ} (hnu : 0≤nu) (hF : 0<F) :
    F*gainC nu B lam h (S/F) 1=gainC nu B lam h S F := by
  have hh := gain_homogeneous_rm (B:=B) (lam:=lam) (h:=h) (S:=S/F) (Q:=1) hnu hF.le
  rw [mul_div_cancel₀ _ hF.ne', mul_one] at hh
  exact hh.symm

/-- Collet's `weighted_exponent_mono` for the repeated-mark gain. -/
theorem weighted_exponent_mono_rm {nu B lam h S L Q : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hlam : 1<lam) (hSL : S≤L) :
    nu*S-gainC nu B lam h S Q≤nu*L-gainC nu B lam h L Q := by
  have hν : 0≤nu := by linarith
  by_cases P : QRH.RepeatedMarks.ParentParams nu 8 B lam h
  · rw [gainC_of P, gainC_of P]
    have hm := QRH.RepeatedMarks.gainK_width_mono P (le_max_right S 0) (max_le_max hSL le_rfl)
      (le_max_right Q 0)
    nlinarith [mul_le_mul_of_nonneg_left (sub_max_zero_mono hSL) hν]
  · rw [gainC_of_not P, gainC_of_not P]
    nlinarith

end
end QRH.Record1252270103Source.High
