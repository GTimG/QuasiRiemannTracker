/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Full preceding-stage cap cover for the actual P.2 rescaled pairs. -/
import Candidate.C092.transport.LowActualStep

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.NativeStrip

/-- Every ordered pair above the preceding closed-stage edge, including the
native top strip. The whole pair is allowed to move under radial rescaling. -/
def EarlierCover (P : ℝ → ℝ → Prop) (y : ℝ) : Prop :=
  ∀ n' y' : ℝ, y/(H : ℝ) ≤ y' → y' ≤ sourceY/(H : ℝ) →
    y' ≤ n' → n' ≤ sourceRatio*y' → P n' y'

/-- Stronger analytic telescope for the same exact 2904-stage induction.
The prefix is strictly earlier in the stage index, with closed shared edges;
no same-stage or later source is used by the new radial calls. -/
theorem ordered_source_induction_cover (P : ℝ → ℝ → Prop)
    (native : ∀ n y, sourceY ≤ y → y ≤ sourceY/(H : ℝ) →
      y ≤ n → n ≤ sourceRatio*y → P n y)
    (step : ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover P y → P n y) :
    ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → P n y := by
  have hH := H_real_bounds.1
  have stretch {x : ℝ} (hx : 0 ≤ x) : x ≤ x/(H : ℝ) :=
    (le_div_iff₀ hH).2 (mul_le_of_le_one_right hx H_real_bounds.2.le)
  have hYY := stretch (source_domain.1.le.trans (source_domain.2.1.le.trans source_domain.2.2.le))
  have aux (j : ℕ) : ∀ n y : ℝ, sourceY0 ≤ y → sourceY*(H : ℝ)^j ≤ y →
      y ≤ sourceY/(H : ℝ) → y ≤ n → n ≤ sourceRatio*y → P n y := by
    induction j with
    | zero =>
      intro n y _ hc ht hn hr
      exact native n y (by simpa using hc) ht hn hr
    | succ j ih =>
      intro n y hb hc ht hn hr
      by_cases hi : sourceY ≤ y
      · exact native n y hi ht hn hr
      have hy := (not_le.mp hi).le
      have hsmall := stretch (source_domain.1.le.trans hb)
      have hnext : sourceY*(H : ℝ)^j ≤ y/(H : ℝ) := (le_div_iff₀ hH).2
        (by simpa only [pow_succ,mul_assoc] using hc)
      apply step n y hb hy hn hr
      intro n' y' hprior htop hord hratio
      exact ih n' y' (hb.trans (hsmall.trans hprior)) (hnext.trans hprior) htop hord hratio
  have hcast : ((Y*H^2904 : ℚ) : ℝ) ≤ ((369/1000 : ℚ) : ℝ) :=
    Rat.cast_le.mpr source_stage_crossing.1
  push_cast at hcast
  have hc : sourceY*(H : ℝ)^2904 ≤ sourceY0 := by
    have heq : (Y : ℝ) = sourceY := by norm_num [Y,sourceY]
    rw [←heq]
    exact hcast
  intro n y hb ht hn hr
  exact aux 2904 n y hb (hc.trans hb) (ht.trans hYY) hn hr

/-- The strengthened preceding-stage cover instantiates the actual source
induction, retaining the genuine native base and open width. -/
theorem all_strips_of_increment_cover
    (hβ : (51/100 : ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (increment : ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover OpenWidth y → OpenWidth n y) :
    ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → OpenWidth n y :=
  ordered_source_induction_cover OpenWidth
    (fun _ _ hy hy' hn hr _ _ hl => native_box hβ hy hy' hn hr hl.le) increment

/-- Literal P.2 low-radius pair, in the source arm before the native seam. -/
theorem earlier_low_pair {P : ℝ → ℝ → Prop} {n y V : ℝ}
    (cover : EarlierCover P y) (hy : 0 ≤ y) (hn : y ≤ n) (hr : n ≤ sourceRatio*y)
    (hV : 0 < V) (hVH : V ≤ (H : ℝ)) (hseam : y/V ≤ sourceY) :
    P (n/V) (y/V) := by
  have hprior : y/(H : ℝ) ≤ y/V := by
    apply (div_le_div_iff₀ H_real_bounds.1 hV).2
    nlinarith [mul_nonneg hy (sub_nonneg.mpr hVH)]
  have hYY : sourceY ≤ sourceY/(H : ℝ) :=
    (le_div_iff₀ H_real_bounds.1).2
      (mul_le_of_le_one_right (by norm_num [sourceY]) H_real_bounds.2.le)
  apply cover _ _ hprior (hseam.trans hYY) (div_le_div_of_nonneg_right hn hV.le)
  simpa [mul_div_assoc] using div_le_div_of_nonneg_right hr hV.le

/-- Literal P.2 adjusted high substitute: both reordered caps, not only the
horizontal H-label pair, are supplied from the true earlier prefix. -/
theorem earlier_adjusted_pair {P : ℝ → ℝ → Prop} {n y m V : ℝ}
    (cover : EarlierCover P y) (hy0 : sourceY0 ≤ y)
    (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y) (hm : y/(H : ℝ) ≤ m)
    (hV : 0 < V) (hVH : V ≤ (H : ℝ)) (hseam : adjustedWitness n m V ≤ sourceY) :
    P (max (n/V) (adjustedWitness n m V)) (min (n/V) (adjustedWitness n m V)) := by
  obtain ⟨hprior,_,htop,hratio,_⟩ := adjustedWitness_source_domain hy0 hn0 hn1 hm hV hVH hseam
  have hYY : sourceY ≤ sourceY/(H : ℝ) :=
    (le_div_iff₀ H_real_bounds.1).2
      (mul_le_of_le_one_right (by norm_num [sourceY]) H_real_bounds.2.le)
  exact cover _ _ hprior (htop.trans hYY)
    ((min_le_left _ _).trans (le_max_left _ _)) hratio

/-- The broad earlier cover includes the old fixed pair used by the genuine
low H-step, so the strengthened induction reuses its completed proof. -/
theorem earlier_H_pair {P : ℝ → ℝ → Prop} {n y : ℝ}
    (cover : EarlierCover P y) (hy : y ≤ sourceY) (hn : y ≤ n) (hr : n ≤ sourceRatio*y) :
    P (n/(H : ℝ)) (y/(H : ℝ)) := by
  apply cover _ _ le_rfl (div_le_div_of_nonneg_right hy H_real_bounds.1.le)
    (div_le_div_of_nonneg_right hn H_real_bounds.1.le)
  simpa [mul_div_assoc] using div_le_div_of_nonneg_right hr H_real_bounds.1.le

end
end QRH.Cycle092.LowActual
