/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Quantitative debit for the coupled positive-cost physical source. This compares
the actual two-branch capacity with the limiting one, without fixing the cap
or discarding either branch. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactReturnRows
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSource

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set

/-- The physical schedule uses cap 3/40, budget 1-s and multiplier 2+10s. -/
def positiveCapacity (s D : ℝ) : ℝ :=
  min ((3/40)*D) ((2*y-(1+s)*D)/(2+10*s))

/-- Uniform one-sided Lipschitz bound for both capacity branches. -/
theorem positive_capacity_lower {s D : ℝ} (hs : 0 ≤ s) (hD : 0 ≤ D) :
    newCapacity D-5*s ≤ positiveCapacity s D := by
  have hy : y ≤ 1 := by linarith [y_bounds.2]
  have hden : 0 < 2+10*s := by positivity
  have hsecond : (2*y-D)/2-5*s ≤ (2*y-(1+s)*D)/(2+10*s) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_nonneg hs (sub_nonneg.mpr hy)
    have hn := mul_nonneg hs hD
    nlinarith [sq_nonneg s]
  unfold positiveCapacity newCapacity
  apply le_min
  · have hm := min_le_left ((3/40)*D) ((2*y-D)/2)
    linarith
  · exact (sub_le_sub_right (min_le_right ((3/40)*D) ((2*y-D)/2)) _).trans hsecond

/-- The entire source perturbation costs at most 15s/16 in the physical row.
The admitted count envelope is unchanged in this comparison. -/
theorem positive_row_debit {s D d p : ℝ} (hs : 0 ≤ s) (hD : 0 ≤ D)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    row D (positiveCapacity s D) d p ≤ row D (newCapacity D) d p+15*s/16 := by
  have hc := positive_capacity_lower hs hD
  have hdp : 0 ≤ d*p := mul_nonneg hd.1 hp.1
  have hdpmax : d*p ≤ (3/8:ℝ) := by
    have hh := mul_le_mul hd.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hh ⊢
    exact hh
  have hm := mul_nonneg hdp (sub_nonneg.mpr hc)
  have hn := mul_nonneg hs (sub_nonneg.mpr hdpmax)
  unfold row price
  nlinarith only [hm,hn]

/-- Complete conductor-range consequence, retaining the actual physical source
debit. This is still a scalar return statement, not a nonvanishing theorem. -/
theorem positive_source_rows {s D d p : ℝ} (hs : 0 ≤ s)
    (hcon : D ∈ Icc (19/25:ℝ) stationaryCutoff)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    row D (positiveCapacity s D) d p ≤ theta+15*s/16 := by
  have hD : 0 ≤ D := le_trans (by norm_num) hcon.1
  have hr := positive_row_debit hs hD hd hp
  have hn := new_rows hcon hd hp
  linarith

def targetEll (t : ℝ) : ℝ := 11/3-4*t
def targetY (t : ℝ) : ℝ := stationaryCutoff-2*targetEll t
def targetCapacity (s t D : ℝ) : ℝ :=
  min ((3/40)*D) ((2*targetY t-(1+s)*D)/(2+10*s))

/-- Target geometry, retaining the already proved count envelope at the exact
root. Transport to the target's count parameter is a separate obligation. -/
def targetRowWithFixedCount (t D cap d p : ℝ) : ℝ :=
  1/2+13*stationaryCutoff/75-targetY t/2-targetEll t/2-9*D/100+
    d/2+d*p*(targetEll t-cap/2)+(3/4)*D*envelope d p

theorem target_capacity_mono {s t D : ℝ} (hs : 0 ≤ s) (ht : theta ≤ t) :
    positiveCapacity s D ≤ targetCapacity s t D := by
  have hden : 0 < 2+10*s := by positivity
  unfold positiveCapacity targetCapacity
  apply min_le_min le_rfl
  apply (div_le_div_iff_of_pos_right hden).mpr
  unfold targetY targetEll y ell
  linarith

theorem target_row_shift (t D cap d p : ℝ) :
    targetRowWithFixedCount t D cap d p = row D cap d p-(2+4*d*p)*(t-theta) := by
  unfold targetRowWithFixedCount targetY targetEll row price ell
  ring

/-- A uniform strict-return margin on the complete upper conductor interval.
Both capacity branches and the source debit are retained. -/
theorem target_positive_rows {s t D d p : ℝ} (hs : 0 ≤ s) (ht : theta ≤ t)
    (hcon : D ∈ Icc (19/25:ℝ) stationaryCutoff)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRowWithFixedCount t D (targetCapacity s t D) d p ≤
      theta+15*s/16-2*(t-theta) := by
  have hm := row_antitone_capacity hd.1 hp.1 D _ _ (target_capacity_mono (D := D) hs ht)
  have hr := positive_source_rows hs hcon hd hp
  have hgain := mul_nonneg (mul_nonneg hd.1 hp.1) (sub_nonneg.mpr ht)
  rw [target_row_shift]
  nlinarith only [hm,hr,hgain]

/-- Any fixed target gap pays a positive source cost and row fee. This theorem
does not claim the physical transport has yet been parameterized. -/
theorem target_rows_with_fee {s t fee D d p : ℝ} (hs : 0 ≤ s) (ht : theta ≤ t)
    (hbudget : 15*s/16+fee < 3*(t-theta))
    (hcon : D ∈ Icc (19/25:ℝ) stationaryCutoff)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    targetRowWithFixedCount t D (targetCapacity s t D) d p < t-fee := by
  have hr := target_positive_rows hs ht hcon hd hp
  linarith

/-- A genuine source and one common positive row fee pay all upper conductor
rows simultaneously. The count parameter is still fixed at the exact root,
and extension of the conductor interval remains a transport obligation. -/
theorem exists_source_and_strict_rows
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {t : ℝ} (ht : theta < t) :
    ∃ s fee : ℝ, 0 < s ∧ s ≤ 1/1000000000 ∧ 0 < fee ∧
      QRH.Record12518109Existence.UniformUnitFaceSource (PositiveSource.face s) ∧
      ∀ D ∈ Icc (19/25:ℝ) stationaryCutoff,
        ∀ d ∈ Icc (0:ℝ) (3/4), ∀ p ∈ Icc (0:ℝ) (1/2),
          targetRowWithFixedCount t D (targetCapacity s t D) d p < t-fee := by
  have hg : 0 < (t-theta)/4 := by linarith
  obtain ⟨s,hs,hslt,hsmax,hsrc⟩ := PositiveSource.arbitrarily_small hβ hg
  refine ⟨s,(t-theta)/4,hs,hsmax,hg,hsrc,?_⟩
  intro D hD d hd p hp
  apply target_rows_with_fee hs.le ht.le _ hD hd hp
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.positive_capacity_lower
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.positive_source_rows
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.target_rows_with_fee
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.exists_source_and_strict_rows
