/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Lower-conductor transport for the exact return. The inverse-capacity
denominator moves with the target count parameter and its cost is retained. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveExtension

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set

def targetOldCapacity (K t D : ℝ) : ℝ := min D (2*targetY t-D)/(6*K)

theorem old_capacity_denominator_debit {K t D : ℝ}
    (hK : kappa ≤ K) (ht : theta ≤ t) (hD : D ≤ (19/25:ℝ)) :
    oldCapacity D-(K-kappa) ≤ targetOldCapacity K t D := by
  have hk : 0 < kappa := by linarith [kappa_bounds.1]
  have hK0 : 0 < K := lt_of_lt_of_le hk hK
  have hcap : oldCapacity D ≤ (1/2:ℝ) := by
    unfold oldCapacity
    apply (div_le_iff₀ (mul_pos (by norm_num) hk)).mpr
    have hm := min_le_left D (2*y-D)
    linarith [kappa_bounds.1]
  have he : oldCapacity D*(6*kappa) = min D (2*y-D) := by
    unfold oldCapacity
    exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hk))
  have hy : y ≤ targetY t := by unfold y targetY targetEll ell; linarith
  have hm : min D (2*y-D) ≤ min D (2*targetY t-D) :=
    min_le_min le_rfl (by linarith)
  have hprod := mul_nonneg (sub_nonneg.mpr hK)
    (show 0 ≤ K-oldCapacity D by linarith [kappa_bounds.1])
  unfold targetOldCapacity
  apply (le_div_iff₀ (mul_pos (by norm_num) hK0)).mpr
  nlinarith only [he,hm,hprod]

/-- Moving both inverse capacity and the admitted count costs at most a quarter
of the target count-parameter increase. -/
theorem target_old_rows {t D d p : ℝ} (ht : theta ≤ t)
    (hcon : D ∈ Icc (1/200:ℝ) (19/25))
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRow (2*t-1) t D (targetOldCapacity (2*t-1) t D) d p ≤
      theta-(3/2)*(t-theta) := by
  have hK : kappa ≤ 2*t-1 := by unfold kappa; linarith
  have hc := old_capacity_denominator_debit hK ht hcon.2
  have hdp : 0 ≤ d*p := mul_nonneg hd.1 hp.1
  have hdpmax : d*p ≤ (3/8:ℝ) := by
    have hh := mul_le_mul hd.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hh ⊢
    exact hh
  have hm := mul_nonneg hdp (sub_nonneg.mpr hc)
  have hn := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hdpmax)
  have hgeom : row D (targetOldCapacity (2*t-1) t D) d p ≤
      row D (oldCapacity D) d p+(3/16)*((2*t-1)-kappa) := by
    unfold row price
    nlinarith only [hm,hn]
  have hD : D ∈ Icc (0:ℝ) 1 := by
    constructor <;> linarith [hcon.1,hcon.2]
  have hcount := target_row_count_debit (t := t)
    (cap := targetOldCapacity (2*t-1) t D) hK hD hd hp
  rw [target_row_shift] at hcount
  have hbase := old_rows hcon hd hp
  have hgain := mul_nonneg hdp (sub_nonneg.mpr ht)
  unfold kappa at hgeom hcount
  nlinarith only [hgeom,hcount,hbase,hgain,sub_nonneg.mpr ht]

/-- One positive fee works throughout both conductor ranges, with genuine
source, target-dependent counts, and a positive upper conductor extension.
The physical analytic consumer remains to be parameterized. -/
theorem exists_positive_complete_return
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {t ε : ℝ} (ht : theta < t) (hε : 0 < ε) :
    ∃ s Δ fee : ℝ, 0 < s ∧ s < ε ∧ s ≤ 1/1000000000 ∧
      0 < Δ ∧ Δ ≤ ε ∧ 0 < fee ∧ fee ≤ ε ∧
      QRH.Record12518109Existence.UniformUnitFaceSource (PositiveSource.face s) ∧
      ∀ D ∈ Icc (1/200:ℝ) (stationaryCutoff+Δ),
        ∀ d ∈ Icc (0:ℝ) (3/4), ∀ p ∈ Icc (0:ℝ) (1/2),
          targetRow (2*t-1) t D
            (if D ≤ 19/25 then targetOldCapacity (2*t-1) t D else targetCapacity s t D)
            d p < t-fee := by
  let b := min ((t-theta)/16) ε
  have hb : 0 < b := lt_min (by linarith) hε
  have hbg : b ≤ (t-theta)/16 := min_le_left _ _
  have hbε : b ≤ ε := min_le_right _ _
  obtain ⟨s,hs,hslt,hsmax,hsrc⟩ := PositiveSource.arbitrarily_small hβ hb
  refine ⟨s,b,b,hs,hslt.trans_le hbε,hsmax,hb,hbε,hb,hbε,hsrc,?_⟩
  intro D hD d hd p hp
  by_cases hswitch : D ≤ 19/25
  · rw [if_pos hswitch]
    have hr := target_old_rows ht.le ⟨hD.1,hswitch⟩ hd hp
    linarith
  · rw [if_neg hswitch]
    have hr := extended_target_rows hs.le ht.le hb.le
      ⟨le_of_not_ge hswitch,hD.2⟩ hd hp
    linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.old_capacity_denominator_debit
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.exists_positive_complete_return
