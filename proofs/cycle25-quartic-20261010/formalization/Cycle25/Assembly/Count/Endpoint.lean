import Cycle25.Assembly.Count.Crossing
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section

def V (δ : ℝ) : ℝ := 5/6-δ
def cutoff (δ p κ : ℝ) : ℝ := 1+δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))
def rowCount (δ p κ : ℝ) : ℝ :=
  1-δ+δ*coefficient p κ*V δ/(2*(V δ+δ*coefficient p κ))

lemma coefficient_nonneg {p κ : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) : 0≤coefficient p κ := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0<denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  unfold coefficient primeWeight
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hd.le

lemma cutoff_bounds {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    1≤cutoff δ p κ ∧ cutoff δ p κ≤3/2 := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hn : 0≤δ*coefficient p κ := mul_nonneg hδ hc
  have hv : 0<V δ := by unfold V; linarith
  have hd : 0<2*(V δ+δ*coefficient p κ) := by positivity
  unfold cutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hn hd.le)
  · have he : δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))≤1/2 :=
      (div_le_iff₀ hd).mpr (by linarith)
    linarith

theorem short_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    shortExponent δ p κ (cutoff δ p κ)=rowCount δ p κ := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hd : V δ+δ*coefficient p κ≠0 := by
    apply ne_of_gt
    have hv : 0<V δ := by unfold V; linarith
    exact add_pos_of_pos_of_nonneg hv (mul_nonneg hδ hc)
  unfold shortExponent cutoff rowCount
  field_simp
  ring

theorem long_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    longExponent δ (cutoff δ p κ)=rowCount δ p κ := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hd : V δ+δ*coefficient p κ≠0 := by
    apply ne_of_gt
    have hv : 0<V δ := by unfold V; linarith
    exact add_pos_of_pos_of_nonneg hv (mul_nonneg hδ hc)
  unfold longExponent HeckeDetectorRowCount.longExponent cutoff rowCount V at *
  field_simp
  ring

theorem max_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    max (shortExponent δ p κ (cutoff δ p κ)) (longExponent δ (cutoff δ p κ))=rowCount δ p κ := by
  rw [short_at_cutoff hδ hδ1 hp hp1 hk hk1,long_at_cutoff hδ hδ1 hp hp1 hk hk1,max_self]
end
end OAI.SevenEighths.Cycle25DetectorRowCount
