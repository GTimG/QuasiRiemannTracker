import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing

/-! Variable plain-moment coefficient for Cycle25. Adapted from pinned
OpenAI DetectorRowCountCrossing (Apache-2.0); original definitions preserved. -/
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section

def b (p κ : ℝ) : ℝ := p/(3*κ)
def denominator (p κ : ℝ) : ℝ := 3-p-2*b p κ
def primeWeight (p κ : ℝ) : ℝ := 2*(1-p)*(1-b p κ)
def coefficient (p κ : ℝ) : ℝ := primeWeight p κ/denominator p κ
def crossing (p κ t : ℝ) : ℝ := ((2-2*b p κ)*t-p+b p κ)/denominator p κ
def inverseExponent (δ p r : ℝ) : ℝ := 1-δ*(p+(1-p)*r)
def plainExponent (δ p κ t r : ℝ) : ℝ := 1-δ*(b p κ+(2-2*b p κ)*(t-r))
def shortExponent (δ p κ t : ℝ) : ℝ := 1-δ+δ*coefficient p κ*(3/2-t)
abbrev longExponent := HeckeDetectorRowCount.longExponent

lemma b_bounds {p κ : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    0≤b p κ ∧ 4*p/9≤b p κ ∧ b p κ≤10*p/21 ∧ b p κ≤p := by
  have hd : 0<3*κ := by linarith
  unfold b
  refine ⟨div_nonneg hp hd.le,(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_⟩
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk1)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]

lemma denominator_lower {p κ : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) : 85/42≤denominator p κ := by
  have hb := b_bounds hp hp1 hk hk1
  unfold denominator
  linarith

theorem crossing_bounds {p κ t : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (ht : 1≤t) (ht1 : t≤3/2) :
    23/37≤crossing p κ t ∧ crossing p κ t≤1 ∧
      1/3≤t-crossing p κ t ∧ t-crossing p κ t≤1/2 := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0<denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  have hpt := mul_le_mul_of_nonneg_left ht (show 0≤2-2*b p κ by linarith)
  have hpt1 := mul_le_mul_of_nonneg_left ht1 (show 0≤2-2*b p κ by linarith)
  have hmt := mul_le_mul_of_nonneg_left ht (show 0≤1-p by linarith)
  have hmt1 := mul_le_mul_of_nonneg_left ht1 (show 0≤1-p by linarith)
  have he : t-crossing p κ t=((1-p)*t+p-b p κ)/denominator p κ := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

lemma inverse_at_crossing (δ p κ t : ℝ) (hd : denominator p κ≠0) :
    inverseExponent δ p (crossing p κ t)=shortExponent δ p κ t := by
  unfold inverseExponent crossing shortExponent coefficient primeWeight
  field_simp
  unfold denominator
  ring
lemma plain_at_crossing (δ p κ t : ℝ) (hd : denominator p κ≠0) :
    plainExponent δ p κ t (crossing p κ t)=shortExponent δ p κ t := by
  unfold plainExponent crossing shortExponent coefficient primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {δ p κ t r : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    (r≤crossing p κ t → plainExponent δ p κ t r≤shortExponent δ p κ t) ∧
      (crossing p κ t≤r → inverseExponent δ p r≤shortExponent δ p κ t) := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : denominator p κ≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1))
  constructor
  · intro hr
    rw [←plain_at_crossing δ p κ t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤2-2*b p κ by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [←inverse_at_crossing δ p κ t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1-p by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

lemma short_ge_base {δ p κ t : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (ht : t≤3/2) : 1-δ≤shortExponent δ p κ t := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0<denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  have hw : 0≤primeWeight p κ := by unfold primeWeight; exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  unfold shortExponent coefficient
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hδ (div_nonneg hw hd.le)) (by linarith))

theorem plain_capacity_comparison {δ p κ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hγ : 0≤γ) (hlength : t-r-γ≤m) :
    1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ)≤plainExponent δ p κ t r+2*γ := by
  have hd : 6*κ≠0 := by linarith
  have hb := b_bounds hp hp1 hk hk1
  have hc : 0≤δ*(2-2*b p κ) := mul_nonneg hδ (by linarith)
  have hc1 : δ*(2-2*b p κ)≤2 := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0≤2-2*b p κ by linarith)
    nlinarith
  have hid : (1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ))-plainExponent δ p κ t r =
      δ*(2-2*b p κ)*(t-r-m) := by unfold plainExponent b; field_simp; ring
  have hl := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have he := mul_le_mul_of_nonneg_right hc1 hγ
  linarith

end
end OAI.SevenEighths.Cycle25DetectorRowCount
