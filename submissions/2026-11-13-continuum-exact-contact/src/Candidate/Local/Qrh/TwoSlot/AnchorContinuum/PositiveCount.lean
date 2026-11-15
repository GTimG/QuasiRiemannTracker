/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Transport the admitted exact count envelope to the positive target parameter.
The old-count branch is not assumed monotone: its existing quantitative gap
bound is charged explicitly. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveCapacity
import Submissions.hailey_collet_1252270103.Record12518109Return.CountingBridge

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set
open Qrh.TwoSlot.AnchorZeroLoss
local instance : Affine.Return.ImprovedCountScheme exactLine := exactScheme

def envelopeAt (K d p : ℝ) : ℝ :=
  Affine.Return.ImprovedCount.envelope (line := exactLine) K d p

theorem envelope_parameter_debit {K d p : ℝ} (hK : kappa ≤ K)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    envelopeAt K d p-envelope d p ≤ 5*(K-kappa)/216 := by
  have hh := QRH.Record12518109Return.envelope_gap
    (Affine.Return.ImprovedCount.admittedBranches (line := exactLine)) kappa_bounds.1 hK
    (show 0 ≤ d ∧ d ≤ 5/6 by constructor <;> linarith [hd.1,hd.2]) hp
  change envelopeAt K d p-envelope d p ≤ _ at hh
  linarith

/-- Physical row at the target count parameter, with its budget-dependent cap. -/
def targetRow (K t D cap d p : ℝ) : ℝ :=
  targetRowWithFixedCount t D cap d p+(3/4)*D*(envelopeAt K d p-envelope d p)

theorem target_row_count_debit {K t D cap d p : ℝ} (hK : kappa ≤ K)
    (hD : D ∈ Icc (0:ℝ) 1)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRow K t D cap d p ≤ targetRowWithFixedCount t D cap d p+(K-kappa)/50 := by
  have hh := envelope_parameter_debit hK hd hp
  have hm := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 3/4) hD.1)
  have hn := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hD.2)
  unfold targetRow
  nlinarith only [hm,hn,sub_nonneg.mpr hK]

/-- Full upper-conductor return at the actual target count parameter. The
parameter debit is paid, rather than suppressed by a monotonicity assertion. -/
theorem target_count_rows {s t D d p : ℝ} (hs : 0 ≤ s) (ht : theta ≤ t)
    (hcon : D ∈ Icc (19/25:ℝ) stationaryCutoff)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRow (2*t-1) t D (targetCapacity s t D) d p ≤
      theta+15*s/16-(49/25)*(t-theta) := by
  have hK : kappa ≤ 2*t-1 := by unfold kappa; linarith
  have hD : D ∈ Icc (0:ℝ) 1 :=
    ⟨le_trans (by norm_num) hcon.1, hcon.2.trans (by linarith [stationaryCutoff_bounds.2])⟩
  have hc := target_row_count_debit (t := t) (cap := targetCapacity s t D) hK hD hd hp
  have hr := target_positive_rows hs ht hcon hd hp
  unfold kappa at hc
  linarith

/-- Genuine source and strict rows, now at the target count parameter. The
positive conductor extension and analytic transport remain separate. -/
theorem exists_source_and_target_count_rows
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {t : ℝ} (ht : theta < t) :
    ∃ s fee : ℝ, 0 < s ∧ s ≤ 1/1000000000 ∧ 0 < fee ∧
      QRH.Record12518109Existence.UniformUnitFaceSource (PositiveSource.face s) ∧
      ∀ D ∈ Icc (19/25:ℝ) stationaryCutoff,
        ∀ d ∈ Icc (0:ℝ) (3/4), ∀ p ∈ Icc (0:ℝ) (1/2),
          targetRow (2*t-1) t D (targetCapacity s t D) d p < t-fee := by
  have hg : 0 < (t-theta)/4 := by linarith
  obtain ⟨s,hs,hslt,hsmax,hsrc⟩ := PositiveSource.arbitrarily_small hβ hg
  refine ⟨s,(t-theta)/4,hs,hsmax,hg,hsrc,?_⟩
  intro D hD d hd p hp
  have hr := target_count_rows hs.le ht.le hD hd hp
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.envelope_parameter_debit
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.exists_source_and_target_count_rows
