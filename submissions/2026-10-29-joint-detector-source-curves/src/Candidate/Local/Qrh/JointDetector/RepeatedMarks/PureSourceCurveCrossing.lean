/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCrossing

namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set

private theorem affine_positive {a b lo hi x : ℝ} (hw : lo < hi)
    (hl : 0 < a+b*lo) (hh : 0 < a+b*hi) (hx : x∈Icc lo hi) : 0<a+b*x := by
  by_cases hb : 0 ≤ b
  · have := mul_le_mul_of_nonneg_left hx.1 hb; linarith
  · have := mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hb); linarith

structure PureCrossing (B L s n : ℝ) : Prop where
  B_pos : 0 < B
  B_le : B ≤ 1
  L_lower : 3/2 ≤ L
  s_pos : 0 < s
  s_cap : s < 1/10
  n_pos : 0 < n
  n_upper : n < 3/4
  derivative_lo : derivativeRay (B-L*s) s 1 n < 0
  derivative_hi : derivativeRay (B-L*s) s 1 (3/4) < 0
  repeated_lo : 0 < repeatedRay (B-L*s) s 1 n
  repeated_hi : 0 < repeatedRay (B-L*s) s 1 (3/4)

namespace PureCrossing
variable {B L s n : ℝ} (h : PureCrossing B L s n)
include h

theorem repeated_gap {ν a : ℝ} (hν : ν∈Icc n (3/4:ℝ))
    (ha : a∈Icc (0:ℝ) ((1:ℝ)*ν)) : 0 < G B L s ν a := by
  have hνpos := h.n_pos.trans_le hν.1
  have hd : derivativeRay (B-L*s) s (1:ℝ) ν < 0 := by
    have hl : 0 < -(5*(B-L*s)/12-5*s/3)+(-(-1+(B-L*s)/2+2*s*(1:ℝ)))*n := by
      have hh := h.derivative_lo; unfold derivativeRay at hh; linarith
    have hh : 0 < -(5*(B-L*s)/12-5*s/3)+(-(-1+(B-L*s)/2+2*s*(1:ℝ)))*(3/4) := by
      have hh := h.derivative_hi; unfold derivativeRay at hh; linarith
    have := affine_positive h.n_upper hl hh hν
    dsimp [derivativeRay]; linarith
  have hp : 0 < repeatedRay (B-L*s) s (1:ℝ) ν := by
    have hl : 0 < (5/3-(B-L*s)*(5/2-5*(1:ℝ)/12)-5*s*(1:ℝ)/3)+
        ((B-L*s)*(1+(1:ℝ)/2)-(1:ℝ)+s*(1:ℝ)^2)*n := by
      have hh := h.repeated_lo; unfold repeatedRay at hh; linarith
    have hh : 0 < (5/3-(B-L*s)*(5/2-5*(1:ℝ)/12)-5*s*(1:ℝ)/3)+
        ((B-L*s)*(1+(1:ℝ)/2)-(1:ℝ)+s*(1:ℝ)^2)*(3/4) := by
      have hh := h.repeated_hi; unfold repeatedRay at hh; linarith
    have := affine_positive h.n_upper hl hh hν
    dsimp [repeatedRay]; linarith
  have hid : G B L s ν ((1:ℝ)*ν)=ν*repeatedRay (B-L*s) s (1:ℝ) ν := by
    unfold G K T repeatedRay; ring
  have hbase : 0 < G B L s ν ((1:ℝ)*ν) := by rw [hid]; exact mul_pos hνpos hp
  have hdiff : G B L s ν a-G B L s ν ((1:ℝ)*ν)=
      (a-(1:ℝ)*ν)*(derivativeRay (B-L*s) s (1:ℝ) ν+s*(a-(1:ℝ)*ν)) := by
    unfold G K T derivativeRay; ring
  have hdif : a-(1:ℝ)*ν ≤ 0 := sub_nonpos.mpr ha.2
  have hm : 0 ≤ (a-(1:ℝ)*ν)*(derivativeRay (B-L*s) s (1:ℝ) ν+s*(a-(1:ℝ)*ν)) :=
    mul_nonneg_of_nonpos_of_nonpos hdif (by nlinarith [mul_nonpos_of_nonneg_of_nonpos h.s_pos.le hdif])
  linarith

theorem denominators {ν a : ℝ} (hν : ν∈Icc n (3/4:ℝ)) (ha : a∈Icc (0:ℝ) ν) :
    0 < T ν a ∧ 0 < L*T ν a-a*K a ∧ 0 < ν*L-a := by
  have hn := h.n_pos.trans_le hν.1
  have hLp : 0 < L := by linarith [h.L_lower]
  have hu : 0 < ν-a/2 := by linarith [ha.2]
  have hV : 0 < (5/6:ℝ)-ν := by linarith [hν.2]
  have hav : a/L ≤ ν/L := div_le_div_of_nonneg_right ha.2 hLp.le
  have hνL : ν/L < ν := (div_lt_iff₀ hLp).2 (by nlinarith [h.L_lower])
  have hv : 0 < 2*(ν-a/L) := by linarith
  have ht : T ν a = (ν-a/2)*(2*ν)+(5/6-ν)*(ν-a/2+2*ν) := by unfold T; ring
  have htpos : 0 < T ν a := by rw [ht]; positivity
  have hd : L*T ν a-a*K a = L*((ν-a/2)*(2*(ν-a/L))+
      (5/6-ν)*(ν-a/2+2*(ν-a/L))) := by unfold T K; field_simp; ring
  have hdpos : 0 < L*T ν a-a*K a := by rw [hd]; positivity
  exact ⟨htpos,hdpos,by nlinarith [h.L_lower,ha.2]⟩

/-- Exact budget-branch crossing gap; this is the literal repeated count. -/
theorem budget_gap_identity {ν a : ℝ} (hν : ν∈Icc n (3/4:ℝ)) (ha : a∈Icc (0:ℝ) ν) :
    1-ν*(B-L*s)-a*s-budgetCrossingRate B L ν (a/(2*ν)) =
      (ν*L-a)*G B L s ν a/(L*T ν a-a*K a) := by
  have hn := h.n_pos.trans_le hν.1
  have hLp : L ≠ 0 := by linarith [h.L_lower]
  have hd := (h.denominators hν ha).2.1.ne'
  have hbranch : crossingDen ν (a/(2*ν)) (2-4*(a/(2*ν))/L)=
      (L*T ν a-a*K a)/(ν*L) := by
    unfold crossingDen T K
    field_simp [hn.ne',hLp]
    <;> ring
  unfold budgetCrossingRate crossingRate
  rw [hbranch]
  field_simp [hn.ne',hLp,hd]
  unfold G T K
  ring

theorem budget_crossing {ν a : ℝ} (hν : ν∈Icc n (3/4:ℝ))
    (ha : a∈Icc (0:ℝ) ((1:ℝ)*ν)) :
    budgetCrossingRate B L ν (a/(2*ν)) < 1-ν*(B-L*s)-a*s := by
  have hn := h.n_pos.trans_le hν.1
  have haν : a ≤ ν := ha.2.trans (by nlinarith [(show (1:ℝ) ≤ 1 from le_rfl)])
  have hden := h.denominators hν ⟨ha.1,haν⟩
  have hid := h.budget_gap_identity hν ⟨ha.1,haν⟩
  have hh := div_pos (mul_pos hden.2.2 (h.repeated_gap hν ha)) hden.2.1
  linarith

theorem cap_budget_difference {ν a : ℝ} (hν : ν∈Icc n (3/4:ℝ))
    (ha : a∈Icc (0:ℝ) ν) :
    capCrossingRate (1/10) ν (a/(2*ν))-budgetCrossingRate B L ν (a/(2*ν)) =
      -a*(5/6-ν)*(ν-a/2)*
      ((1/10)-(B*T ν a-ν*K a)/(L*T ν a-a*K a))/(T ν a) := by
  have hn := h.n_pos.trans_le hν.1
  have hLp : L ≠ 0 := by linarith [h.L_lower]
  have hds := h.denominators hν ha
  have hdcap : crossingDen ν (a/(2*ν)) 2=T ν a/ν := by
    unfold crossingDen T; field_simp [hn.ne']; ring
  have hdbudget : crossingDen ν (a/(2*ν)) (2-4*(a/(2*ν))/L)=
      (L*T ν a-a*K a)/(ν*L) := by
    unfold crossingDen T K; field_simp [hn.ne',hLp]; ring
  unfold capCrossingRate budgetCrossingRate crossingRate
  rw [hdcap,hdbudget]
  have hd : T ν a*L-K a*a ≠ 0 := by nlinarith [hds.2.1]
  have hd2 : T ν a*L-a*K a ≠ 0 := by nlinarith [hds.2.1]
  field_simp [hn.ne',hLp,hds.1.ne',hds.2.1.ne',hd,hd2]
  unfold T K
  ring

theorem raw_crossing {ν a : ℝ} (hν : ν∈Icc n (3/4:ℝ))
    (ha : a∈Icc (0:ℝ) ((1:ℝ)*ν)) :
    rawRepeatedCountRate B L (1/10) ν a < 1-ν*(B-L*s)-a*s := by
  have hn := h.n_pos.trans_le hν.1
  have haν : a ≤ ν := ha.2.trans (by nlinarith [(show (1:ℝ) ≤ 1 from le_rfl)])
  have hds := h.denominators hν ⟨ha.1,haν⟩
  have hzid : s-(B*T ν a-ν*K a)/(L*T ν a-a*K a)=
      G B L s ν a/(L*T ν a-a*K a) := by
    apply (eq_div_iff hds.2.1.ne').2
    rw [sub_mul,div_mul_cancel₀ _ hds.2.1.ne']
    unfold G; ring
  have hz : (B*T ν a-ν*K a)/(L*T ν a-a*K a) < s := by
    have hp := div_pos (h.repeated_gap hν ha) hds.2.1
    linarith
  have hdiff := h.cap_budget_difference hν ⟨ha.1,haν⟩
  have hnonpos : capCrossingRate (1/10) ν (a/(2*ν)) ≤
      budgetCrossingRate B L ν (a/(2*ν)) := by
    have ht : 0 ≤ a*(5/6-ν)*(ν-a/2)*
        ((1/10)-(B*T ν a-ν*K a)/(L*T ν a-a*K a))/(T ν a) := by
      apply div_nonneg _ hds.1.le
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg ha.1 (by linarith [hν.2])) (by linarith)
      · linarith [h.s_cap]
    have hneg : -a*(5/6-ν)*(ν-a/2)*
        ((1/10)-(B*T ν a-ν*K a)/(L*T ν a-a*K a))/(T ν a) =
        -(a*(5/6-ν)*(ν-a/2)*
        ((1/10)-(B*T ν a-ν*K a)/(L*T ν a-a*K a))/(T ν a)) := by ring
    rw [hneg] at hdiff
    linarith
  have hb := h.budget_crossing hν ha
  have htail : 1-ν*B < 1-ν*(B-L*s)-a*s := by
    have := mul_pos hds.2.2 h.s_pos
    nlinarith
  exact max_lt (max_lt (hnonpos.trans_lt hb) hb) htail


end PureCrossing
end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.PureCrossing.raw_crossing
