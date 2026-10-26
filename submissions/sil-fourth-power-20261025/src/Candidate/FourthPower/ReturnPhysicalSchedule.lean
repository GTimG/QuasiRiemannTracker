/- Copyright (c) 2026 Sil. Apache-2.0.
Full-source reflected schedule at the certified cutoff 1/250.
Adapted from PR69 PhysicalDirect/Geometry and ClippedCapacityDamping.
Only scalar facts are proved here; no physical moment is an assumption.
 -/
import Candidate.FourthPower.ReturnAnalyticFinish

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnPhysicalSchedule
noncomputable section
open scoped Classical BigOperators
open ReturnCertificate

def shiftBase (d : ℝ) : ℝ := 2*y/d-1
def oldShiftCapacity (b t : ℝ) : ℝ := max 0 ((b-2*t)/(9/2))

/-- v is twice the plain-length shift. The genuine cutoff is t=1/250. -/
def scheduledCapacity (d v : ℝ) : ℝ :=
  if v ≤ 2*shiftCutoff then shiftedWidth d (v/2)
  else oldShiftCapacity (shiftBase d) (v/2)

theorem base_width_identity (d : ℝ) :
    shiftedWidth d 0 = widthAt (shiftBase d) := by
  unfold shiftedWidth widthAt shiftedPlain shiftBase
  congr 1
  ring

theorem scheduled_capacity_nonneg {d v : ℝ}
    (hd : ds ≤ d ∧ d ≤ dplus) (hv : 0 ≤ v) :
    0 ≤ scheduledCapacity d v := by
  unfold scheduledCapacity
  split_ifs with hs
  · have hw := (shifted_global_source_domain hd.1 hd.2
      (show 0 ≤ v/2 by linarith) (show v/2 ≤ shiftCutoff by linarith)).2.1
    exact hw.le
  · exact le_max_left _ _

/-- The scheduled marked family fits inside the genuine available slot supply. -/
theorem scheduled_capacity_le_supply {d v : ℝ}
    (hd : ds ≤ d ∧ d ≤ dplus) (hv : 0 ≤ v) :
    scheduledCapacity d v ≤ ell/d := by
  have hds : 0 < ds := by rw [joins_exact.1]; norm_num
  have hd0 : 0 < d := hds.trans_le hd.1
  have hell : 0 ≤ ell := by rw [parameters_exact.2.1]; norm_num
  have hdiv := div_le_div_of_nonneg_left hell hd0 hd.2
  have hs : (1/5:ℝ) < ell/d := by
    linarith [complementary_guards.supply]
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hh : shiftedWidth d (v/2) ≤ sPhysical := min_le_left _ _
    norm_num [sPhysical] at hh
    linarith
  · have hy : 0 ≤ 2*y := by rw [parameters_exact.2.2.2]; norm_num
    have hi := div_le_div_of_nonneg_left hy hds hd.1
    have hb : 2*y/ds-1 ≤ (9/50:ℝ) := by
      norm_num [ds,kappa,theta,y,ell,h]
    have hb' : shiftBase d ≤ 9/50 := by
      unfold shiftBase
      linarith
    have hc : oldShiftCapacity (shiftBase d) (v/2) ≤ (1/25:ℝ) := by
      unfold oldShiftCapacity
      apply max_le
      · norm_num
      · linarith
    linarith

/-- The relative physical capacity is exactly the certified Z-scale capacity. -/
theorem scaled_zero_capacity {d : ℝ} (hd : 0 < d) :
    d*shiftedWidth d 0 = newCapacity d := by
  unfold shiftedWidth newCapacity
  rw [mul_min_of_nonneg _ _ hd.le]
  congr 1
  · ring
  · unfold shiftedPlain
    field_simp [hd.ne']
    <;> ring

/-- Every selected slot family lies either in our full-source small-shift
domain or in the inherited natural large-shift/empty-family domain. -/
theorem scheduled_capacity_or_empty {α : Type*}
    (T : Finset α) (width : T → ℝ) {d t k : ℝ}
    (hd : ds ≤ d ∧ d ≤ dplus) (ht : 0 ≤ t) (hk : k ≤ 3/4)
    (hw : ∀ i, 0 < width i)
    (hselected : (∑ i,width i) ≤ scheduledCapacity d (2*t)) :
    (∃ d' t' : ℝ, ds ≤ d' ∧ d' ≤ dplus ∧ 0 ≤ t' ∧ t' ≤ shiftCutoff ∧
      shiftedPlain d t = shiftedPlain d' t' ∧
      (∑ i,width i) ≤ shiftedWidth d' t') ∨
      (2*shiftedPlain d t+6*k*(∑ i,width i) ≤ 1 ∨ T=∅) := by
  have hsum : 0 ≤ ∑ i,width i := Finset.sum_nonneg (fun i _ => (hw i).le)
  by_cases hsmall : t ≤ shiftCutoff
  · left
    refine ⟨d,t,hd.1,hd.2,ht,hsmall,rfl,?_⟩
    simpa [scheduledCapacity,show 2*t ≤ 2*shiftCutoff by linarith] using hselected
  · right
    have hs : (∑ i,width i) ≤ oldShiftCapacity (shiftBase d) t := by
      simpa [scheduledCapacity,show ¬ 2*t ≤ 2*shiftCutoff by linarith] using hselected
    by_cases hraw : 0 ≤ (shiftBase d-2*t)/(9/2)
    · left
      have hslots : (∑ i,width i) ≤ (shiftBase d-2*t)/(9/2) := by
        simpa [oldShiftCapacity,max_eq_right hraw] using hs
      have hbudget : 2*shiftedPlain d t+(9/2)*(∑ i,width i) ≤ 1 := by
        unfold shiftedPlain shiftBase at *
        rw [mul_div_assoc] at hslots
        linarith
      nlinarith only [hbudget,hk,hsum]
    · right
      have hslots : (∑ i,width i) ≤ 0 := by
        simpa [oldShiftCapacity,max_eq_left (le_of_not_ge hraw)] using hs
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hsng := Finset.single_le_sum
        (fun (j : T) (_ : j ∈ Finset.univ) => (hw j).le)
        (Finset.mem_univ (⟨i,hi⟩ : T))
      linarith [hw ⟨i,hi⟩]

/-- Complete clipped tail reserve, including b<=2t. No upper bound on b. -/
theorem large_capacity_reserve {b t : ℝ} (ht : shiftCutoff ≤ t) :
    t/500 ≤ t/2-(widthAt b-oldShiftCapacity b t)/4 := by
  have ht0 : 0 ≤ t := (by norm_num [shiftCutoff] : (0:ℝ) ≤ shiftCutoff).trans ht
  by_cases hb : b ≤ 2*t
  · have hz : (b-2*t)/(9/2) ≤ 0 := by linarith
    have hr := clipped_shift_saving ht0 hb
    rw [oldShiftCapacity,max_eq_left hz]
    linarith
  · have hz : 0 ≤ (b-2*t)/(9/2) := by linarith
    have hr := large_shift_saving (b:=b) ht
    have he : 0 < eta := by norm_num [eta]
    rw [oldShiftCapacity,max_eq_right hz]
    linarith

/-- The physical coefficient-bin damping rate 1/1000 is preserved at our
larger cutoff. Both empty and positive old-capacity branches are included. -/
theorem scheduled_capacity_damping {d v q δ : ℝ}
    (hv : 0 ≤ v) (hq : 0 ≤ q) (hqd : q ≤ δ/2) (hδ : 0 ≤ δ) :
    q*shiftedWidth d 0/2+(1/1000)*δ*v ≤
      δ*v/4+q*scheduledCapacity d v/2 := by
  by_cases hs : v ≤ 2*shiftCutoff
  · have hr := small_shift_saving d hδ hq hqd (show 0 ≤ v/2 by linarith)
    rw [scheduledCapacity,if_pos hs]
    linarith only [hr]
  · have hr := large_capacity_reserve (b:=shiftBase d)
      (show shiftCutoff ≤ v/2 by linarith)
    rw [←base_width_identity] at hr
    rw [scheduledCapacity,if_neg hs]
    by_cases hL : 0 ≤ shiftedWidth d 0-oldShiftCapacity (shiftBase d) (v/2)
    · have hm := mul_le_mul_of_nonneg_right hqd hL
      have hp := mul_le_mul_of_nonneg_left hr hδ
      nlinarith only [hm,hp]
    · have hm := mul_nonpos_of_nonneg_of_nonpos hq (le_of_not_ge hL)
      have hp := mul_nonneg hδ hv
      nlinarith only [hm,hp]

end
end Candidate.FourthPower.ReturnPhysicalSchedule
