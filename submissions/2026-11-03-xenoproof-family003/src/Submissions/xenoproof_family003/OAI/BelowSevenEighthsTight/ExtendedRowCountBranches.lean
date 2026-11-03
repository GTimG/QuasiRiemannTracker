import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedRowCountEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- Generalization of the numerical branch assembly in the pinned
   DetectorRowCountOptimization.lean. The four analytic estimates are explicit
   hypotheses. This theorem does not construct them from moment estimates. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.RowCountExtension
noncomputable section

def longExponent (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)

theorem short_ge_base {c δ x t : ℝ}
    (hc : 4/9 ≤ c) (hcu : c ≤ 6/13) (hδ : 0 ≤ δ)
    (hx : 0 ≤ x) (hxu : x ≤ 1/2) (ht : t ≤ 3/2) :
    1-δ ≤ shortExponent c δ x t := by
  have hd : 0 < denominator c x :=
    lt_of_lt_of_le (by norm_num) (denominator_lower hc hcu hx hxu)
  have hcx := mul_le_mul hcu hxu hx (by norm_num : (0:ℝ) ≤ 6/13)
  have hp : 0 ≤ primeWeight c x := mul_nonneg (by nlinarith) (by linarith)
  unfold shortExponent
  exact le_add_of_nonneg_right
    (mul_nonneg (div_nonneg (mul_nonneg hδ hp) hd.le) (by linarith))

theorem plain_capacity_comparison {δ x Δ t r m γ κ₀ κ : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ ≤ 1) (hx : 0 ≤ x) (hxu : x ≤ 1/2)
    (hk₀ : 13/18 ≤ κ₀) (hk₀u : κ₀ ≤ 3/4) (hk : κ = κ₀+2*Δ)
    (hΔ : 0 ≤ Δ) (hΔu : Δ ≤ 1) (hm : 1/3-γ ≤ m) (hmu : m ≤ 1/2)
    (hγ : 0 ≤ γ) (hlength : t-r-γ ≤ m) :
    1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ) ≤
      plainExponent (1/(3*κ₀)) δ x t r+Δ/4+4*γ := by
  have hk0p : 0 < κ₀ := by linarith
  have hkp : 0 < κ := by linarith
  have hqu : δ*x ≤ 1/2 :=
    (mul_le_mul hδu hxu hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss_with_length_error (δ*x) m κ₀ κ Δ γ
    hqu hm hmu hk₀ hk hΔ hΔu hγ
  have hrange := reciprocal_range κ₀ hk₀ hk₀u
  have hcx := mul_le_mul hrange.2 hxu hx (by norm_num : (0:ℝ) ≤ 6/13)
  have hcoef : 0 ≤ 2-2*(1/(3*κ₀))*x := by nlinarith
  have hcoef0 : 0 ≤ δ*(2-2*(1/(3*κ₀))*x) := mul_nonneg hδ hcoef
  have hcoef2 : δ*(2-2*(1/(3*κ₀))*x) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hδu hcoef
    have hh' := mul_nonneg (by linarith : 0 ≤ 1/(3*κ₀)) hx
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t-r-m ≤ γ by linarith) hcoef0
  have herror := mul_le_mul_of_nonneg_right hcoef2 hγ
  have hid : (1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ₀))-
      plainExponent (1/(3*κ₀)) δ x t r = δ*(2-2*(1/(3*κ₀))*x)*(t-r-m) := by
    unfold plainExponent
    field_simp
    ring
  have hid' : 1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ) =
      (1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ₀))+
      (δ*x)*(1-2*m)/3*(1/κ₀-1/κ) := by
    field_simp
    ring
  rw [hid']
  linarith

theorem inverse_zero_capacity {δ r ν : ℝ} (hδ : 0 ≤ δ)
    (hcap : (1-r)/2 ≤ ν) : 1-δ*r ≤ 1-δ+2*δ*ν := by
  have hh := mul_le_mul_of_nonneg_left hcap hδ
  nlinarith

theorem plain_zero_capacity {δ m κ ν : ℝ} (hδ : 0 ≤ δ)
    (hk : 0 < κ) (hku : κ ≤ 1) (hν : 0 ≤ ν)
    (hcap : (1-2*m)/(6*κ) ≤ ν) : 1-2*δ*m ≤ 1-δ+6*δ*ν := by
  have hh := (div_le_iff₀ (show 0 < 6*κ by positivity)).mp hcap
  have hkν := mul_le_mul_of_nonneg_right hku hν
  have hm : 1-2*m ≤ 6*ν := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hm hδ
  nlinarith

theorem long_count_bound {δ r t γ : ℝ} (hδ : δ ≤ 5/6)
    (hr : r ≤ t+γ) :
    1-5/6+(5/6-δ)*r ≤ longExponent δ t+(5/6-δ)*γ := by
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5/6-δ by linarith)
  unfold longExponent
  nlinarith

theorem count_bound_of_source_branches (B C U δ x Δ t r m ε ν γ κ₀ κ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδu : δ ≤ 5/6)
    (hx : 0 ≤ x) (hxu : x ≤ 1/2) (hΔ : 0 ≤ Δ)
    (hk₀ : 13/18 ≤ κ₀) (hk₀u : κ₀ ≤ 3/4) (hk : κ = κ₀+2*Δ) (hku : κ ≤ 1)
    (ht : 1 ≤ t) (htu : t ≤ 3/2) (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t-r-γ ≤ m) (hright : r ≤ t+γ)
    (hI0 : B ≤ C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B ≤ C*U^(1-2*δ*m+ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 →
      B ≤ C*U^(inverseExponent δ x r+ε))
    (hP : r ≤ crossing (1/(3*κ₀)) x t → m < 1/2 → ν < (1-2*m)/(6*κ) →
      B ≤ C*U^(1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ)+ε)) :
    B ≤ C*U^(max (shortExponent (1/(3*κ₀)) δ x t) (longExponent δ t)+
      Δ/4+ε+6*ν+5*γ) := by
  let target := max (shortExponent (1/(3*κ₀)) δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ
  have hshort : shortExponent (1/(3*κ₀)) δ x t ≤
      max (shortExponent (1/(3*κ₀)) δ x t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t ≤
      max (shortExponent (1/(3*κ₀)) δ x t) (longExponent δ t) := le_max_right _ _
  have hc := reciprocal_range κ₀ hk₀ hk₀u
  have hbase := short_ge_base hc.1 hc.2 hδ hx hxu htu
  have hcross := crossing_bounds hc.1 hc.2 hx hxu ht htu
  have hchoose := selected_short_bound (t:=t) (r:=r) hc.1 hc.2 hδ hx hxu
  have promote (p : ℝ) (hp : B ≤ C*U^p) (hpt : p ≤ target) : B ≤ C*U^target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1+5*r)/6) = (1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδu hright
    dsimp [target]
    have hcγ : (5/6-δ)*γ ≤ γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing (1/(3*κ₀)) x t ≤ r
  · by_cases hcap : (1-r)/2 ≤ ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2*δ*ν ≤ 6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδu) hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r ≤ crossing (1/(3*κ₀)) x t := (lt_of_not_ge hrc).le
  by_cases hm : 1/2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m < 1/2 := lt_of_not_ge hm
  by_cases hcap : (1-2*m)/(6*κ) ≤ ν
  · apply promote _ hP0
    have hkp : 0 < κ := by linarith
    have hz := plain_zero_capacity hδ hkp hku hν hcap
    have hv : 6*δ*ν ≤ 6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδu) hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1/3-γ ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ ≤ 1 by linarith) hx hxu
      hk₀ hk₀u hk hΔ (show Δ ≤ 1 by linarith) hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

#print axioms plain_capacity_comparison
#print axioms count_bound_of_source_branches
end
end BelowSevenEighthsTight.RowCountExtension
