/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open QRH.Record1252270103Source

/-- A common downward scaling weakens a source face whose budget is
nonnegative at the cap. This transports the rational joins between curve pieces. -/
theorem source_common_scaling {B L c t : ℝ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (_ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hbudget : 0 ≤ B-L*c) (hsource : GlobalSource B L c) :
    GlobalSource (t*B) (t*L) c := by
  apply RestartSourceDomain.uniform_source_of_contains (hsource := hsource)
  apply RestartSourceDomain.global_contains_global hc le_rfl
  have hdiff : 0 ≤ L-t*L := by nlinarith
  rw [max_eq_left hdiff]
  have hpay := mul_nonneg (sub_nonneg.mpr ht1) hbudget
  nlinarith

/-- Increasing the reciprocal slope coordinate scales both source parameters
by the same factor. No source limit is used at a rounded polynomial endpoint. -/
theorem source_reciprocal_join {q y y' c : ℝ}
    (hq : 0 < q) (hy : 0 < y) (hyy : y ≤ y') (hc : 0 ≤ c)
    (hbudget : 0 ≤ (1+q)/(6*q*y)-(1/y)*c)
    (hsource : GlobalSource ((1+q)/(6*q*y)) (1/y) c) :
    GlobalSource ((1+q)/(6*q*y')) (1/y') c := by
  have hy' : 0 < y' := hy.trans_le hyy
  have ht : 0 ≤ y/y' := (div_pos hy hy').le
  have ht1 : y/y' ≤ 1 := (div_le_one hy').2 hyy
  have hs := source_common_scaling hc (by positivity : 0 ≤ 1/y) ht ht1 hbudget hsource
  have hB : (y/y')*((1+q)/(6*q*y)) = (1+q)/(6*q*y') := by field_simp [ne_of_gt hy, ne_of_gt hy', ne_of_gt hq]
  have hL : (y/y')*(1/y) = 1/y' := by field_simp [ne_of_gt hy, ne_of_gt hy', ne_of_gt hq]
  simpa only [hB,hL] using hs

end
end Qrh.JointDetector.RepeatedMarks
#print axioms Qrh.JointDetector.RepeatedMarks.source_reciprocal_join
