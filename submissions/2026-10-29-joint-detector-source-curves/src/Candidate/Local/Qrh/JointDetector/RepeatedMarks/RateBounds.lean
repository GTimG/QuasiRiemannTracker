/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Minimax

/-! Full-capacity repeated-mark count. Both affine plain branches and the
no-slot tail are retained, and the unmarked count remains available. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

def capCrossingRate (c ν p : ℝ) : ℝ := crossingRate ν p 2 (2*p*c)
def budgetCrossingRate (B L ν p : ℝ) : ℝ := crossingRate ν p (2-4*p/L) (2*p*B/L)
def unmarkedCountRate (ν : ℝ) : ℝ := 1-10*ν/(15-6*ν)
def repeatedCountRate (B L c ν v : ℝ) : ℝ :=
  min (unmarkedCountRate ν)
    (max (max (capCrossingRate c ν (v/(2*ν))) (budgetCrossingRate B L ν (v/(2*ν)))) (1-ν*B))

theorem crossing_lower {ν p A Z : ℝ} (hν : 0 ≤ ν) (hνhi : ν ≤ 5/6)
    (hp : p ≤ 1) (hZ : Z ≤ 1) (hJ : 0 < crossingDen ν p A) :
    1-ν ≤ crossingRate ν p A Z := by
  unfold crossingRate
  have hterm : 0 ≤ (5/6-ν)*ν*(1-p)*(1-Z)/crossingDen ν p A := by
    exact div_nonneg (by positivity) hJ.le
  linarith

theorem branch_den_pos {ν p A : ℝ} (hν : 0 < ν) (hνhi : ν ≤ 3/4)
    (hp : p ≤ 1/2) (hA : 0 < A) : 0 < crossingDen ν p A := by
  have hp1 : 0 < 1-p := by linarith
  have hD : 0 < A+1-p := by linarith
  have hV : 0 < (5/6:ℝ)-ν := by linarith
  unfold crossingDen
  positivity

theorem budget_coefficients {B L p : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hL : 3/2 ≤ L) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    (2/3:ℝ) ≤ 2-4*p/L ∧ 0 ≤ 2*p*B/L ∧ 2*p*B/L ≤ 2/3 := by
  have hL0 : 0 < L := by linarith
  have hq : 4*p/L ≤ 4/3 := (div_le_iff₀ hL0).mpr (by linarith)
  have hZ0 : 0 ≤ 2*p*B/L := by positivity
  have hprod : 2*p*B ≤ 1 := by nlinarith
  have hZhi : 2*p*B/L ≤ 2/3 := (div_le_iff₀ hL0).mpr (by linarith)
  exact ⟨by linarith,hZ0,hZhi⟩

theorem unmarked_bounds {ν : ℝ} (hν : 0 ≤ ν) (hνhi : ν ≤ 3/4) :
    1-ν ≤ unmarkedCountRate ν ∧ unmarkedCountRate ν ≤ 1 := by
  have hden : 0 < 15-6*ν := by linarith
  have hdiv : 10*ν/(15-6*ν) ≤ ν :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  have hdiv0 : 0 ≤ 10*ν/(15-6*ν) := by positivity
  unfold unmarkedCountRate
  constructor <;> linarith

/-- These bounds give the global all-real price its monotonicity and
coordinate Lipschitz constants. They do not clip the physical slot width. -/
theorem repeatedCountRate_bounds {B L c ν v : ℝ}
    (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : 3/2 ≤ L)
    (hc : c ≤ 1/6) (hν : 0 < ν) (hνhi : ν ≤ 3/4)
    (hv0 : 0 ≤ v) (hv : v ≤ ν) :
    1-ν ≤ repeatedCountRate B L c ν v ∧ repeatedCountRate B L c ν v ≤ unmarkedCountRate ν := by
  let p := v/(2*ν)
  have hp0 : 0 ≤ p := div_nonneg hv0 (by positivity)
  have hp : p ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 2*ν)).mpr (by linarith)
  have hcoef := budget_coefficients hB0 hB hL hp0 hp
  have hcapJ := branch_den_pos hν hνhi hp (by norm_num : (0:ℝ)<2)
  have hbudgetJ := branch_den_pos hν hνhi hp (by linarith : 0 < 2-4*p/L)
  have hZcap : 2*p*c ≤ 1 := by
    by_cases hcc : 0 ≤ c
    · nlinarith
    · have : 2*p*c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hcc)
      linarith
  have hcap : 1-ν ≤ capCrossingRate c ν p :=
    crossing_lower hν.le (by linarith) (by linarith) hZcap hcapJ
  have hbudget : 1-ν ≤ budgetCrossingRate B L ν p :=
    crossing_lower hν.le (by linarith) (by linarith) (by linarith) hbudgetJ
  have htail : 1-ν ≤ 1-ν*B := by nlinarith
  constructor
  · apply le_min (unmarked_bounds hν.le hνhi).1
    exact le_max_of_le_right htail
  · exact min_le_left _ _

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

def rawRepeatedCountRate (B L c ν v : ℝ) : ℝ :=
  max (max (capCrossingRate c ν (v/(2*ν)))
    (budgetCrossingRate B L ν (v/(2*ν)))) (1-ν*B)

theorem crossing_upper {ν p A Z : ℝ} (hν : 0 ≤ ν) (hνhi : ν ≤ 5/6)
    (hp : p ≤ 1) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hJ : 0 < crossingDen ν p A) :
    crossingRate ν p A Z ≤ 1 := by
  have hV : 0 ≤ (5/6:ℝ)-ν := by linarith
  have hp0 : 0 ≤ 1-p := by linarith
  have hid : crossingDen ν p A-(5/6-ν)*(1-p)*(1-Z) =
      (5/6-ν)*(A+(1-p)*Z)+ν*(1-p)*A := by unfold crossingDen; ring
  have hdiff : 0 ≤ crossingDen ν p A-(5/6-ν)*(1-p)*(1-Z) := by
    rw [hid]; positivity
  have hdiv : (5/6-ν)*ν*(1-p)*(1-Z)/crossingDen ν p A ≤ ν := by
    apply (div_le_iff₀ hJ).mpr
    have hh := mul_nonneg hν hdiff
    nlinarith only [hh]
  unfold crossingRate
  linarith

theorem rawRepeatedCountRate_bounds {B L c ν v : ℝ}
    (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : 3/2 ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hν : 0 < ν) (hνhi : ν ≤ 3/4)
    (hv0 : 0 ≤ v) (hv : v ≤ ν) :
    1-ν ≤ rawRepeatedCountRate B L c ν v ∧ rawRepeatedCountRate B L c ν v ≤ 1 := by
  let p := v/(2*ν)
  have hp0 : 0 ≤ p := div_nonneg hv0 (by positivity)
  have hp : p ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 2*ν)).mpr (by linarith)
  have hcoef := budget_coefficients hB0 hB hL hp0 hp
  have hcapJ := branch_den_pos hν hνhi hp (by norm_num : (0:ℝ)<2)
  have hbudgetJ := branch_den_pos hν hνhi hp (by linarith : 0 < 2-4*p/L)
  have hcap : capCrossingRate c ν p ≤ 1 :=
    crossing_upper hν.le (by linarith) (by linarith) (by norm_num) (by positivity) hcapJ
  have hbudget : budgetCrossingRate B L ν p ≤ 1 :=
    crossing_upper hν.le (by linarith) (by linarith) (by linarith) hcoef.2.1 hbudgetJ
  constructor
  · apply le_max_of_le_right
    nlinarith
  · exact max_le (max_le hcap hbudget) (by nlinarith)

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

private theorem cutoff_of_room {ν p A Z : ℝ} (hν : 0 < ν)
    (hp : p < 1) (hZ : Z < 1) (hJ : 0 < crossingDen ν p A)
    (hroom : 2*ν*(1-p)*(1-Z) < crossingDen ν p A) :
    1 < crossingCut ν p A Z ∧ crossingCut ν p A Z < 3/2 := by
  have hnum : 0 < ν*(1-p)*(1-Z) := by positivity
  have hdiv : 0 < ν*(1-p)*(1-Z)/crossingDen ν p A := div_pos hnum hJ
  have hdivhi : ν*(1-p)*(1-Z)/crossingDen ν p A < 1/2 :=
    (div_lt_iff₀ hJ).mpr (by linarith)
  unfold crossingCut
  constructor <;> linarith

theorem cap_cutoff_bounds {ν p c : ℝ} (hν : 0 < ν) (hνhi : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hc0 : 0 ≤ c) (hc : c ≤ 1/6) :
    1 < crossingCut ν p 2 (2*p*c) ∧ crossingCut ν p 2 (2*p*c) < 3/2 := by
  have hJ := branch_den_pos hν hνhi hp (by norm_num : (0:ℝ)<2)
  have hZ : 2*p*c < 1 := by nlinarith
  apply cutoff_of_room hν (by linarith) hZ hJ
  have hid : crossingDen ν p 2-2*ν*(1-p)*(1-2*p*c) =
      (5/6-ν)*(3-p)+4*ν*p*(1-p)*c := by unfold crossingDen; ring
  have hleft : 0 < (5/6-ν)*(3-p) := mul_pos (by linarith) (by linarith)
  have hp1 : 0 ≤ 1-p := by linarith
  have hright : 0 ≤ 4*ν*p*(1-p)*c := by positivity
  nlinarith only [hid,hleft,hright]

theorem budget_cutoff_bounds {B L ν p : ℝ}
    (hB0 : 9/10 ≤ B) (hB : B ≤ 1) (hL : 3/2 ≤ L)
    (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    1 < crossingCut ν p (2-4*p/L) (2*p*B/L) ∧
      crossingCut ν p (2-4*p/L) (2*p*B/L) < 3/2 := by
  have hL0 : 0 < L := by linarith
  have hcoef := budget_coefficients (by linarith : 0≤B) hB hL hp0 hp
  have hJ := branch_den_pos hν hνhi hp (by linarith : 0<2-4*p/L)
  apply cutoff_of_room hν (by linarith) (by linarith) hJ
  have hpq0 : 0 ≤ p*(1-p) := mul_nonneg hp0 (by linarith)
  have hpq : p*(1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
  have hproduct := mul_le_mul hνhi hpq hpq0 (by norm_num : (0:ℝ)≤3/4)
  have hprod0 : 0 ≤ ν*(p*(1-p)) := mul_nonneg hν.le hpq0
  have hproduct' := mul_le_mul hproduct (show 1-B ≤ (1/10:ℝ) by linarith)
    (show 0 ≤ 1-B by linarith) (by norm_num : (0:ℝ)≤(3/4)*(1/4))
  have hcost : 4*ν*p*(1-p)*(1-B)/L ≤ 1/20 := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith only [hproduct',hL]
  have hD : 7/6 ≤ (2-4*p/L)+1-p := by linarith [hcoef.1]
  have hV : 1/12 ≤ (5/6:ℝ)-ν := by linarith
  have hmain := mul_le_mul hV hD (by norm_num : (0:ℝ)≤7/6)
    (by linarith : 0≤(5/6:ℝ)-ν)
  have hid : crossingDen ν p (2-4*p/L)-2*ν*(1-p)*(1-2*p*B/L) =
      (5/6-ν)*((2-4*p/L)+1-p)-4*ν*p*(1-p)*(1-B)/L := by
    unfold crossingDen
    field_simp [hL0.ne']
    <;> ring
  nlinarith only [hid,hmain,hcost]

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

theorem cap_cutoff_gap {ν p c : ℝ} (hν : 0<ν) (hνhi : ν≤3/4)
    (hp0 : 0≤p) (hp : p≤1/2) (hc0 : 0≤c) (hc : c≤1/6) :
    1+ν/10≤crossingCut ν p 2 (2*p*c) := by
  have hJ := branch_den_pos hν hνhi hp (by norm_num : (0:ℝ)<2)
  have hZ : 2*p*c≤1/6 := by nlinarith
  have hU : 5/12≤(1-p)*(1-2*p*c) := by
    have hh := mul_le_mul (show (1/2:ℝ)≤1-p by linarith)
      (show (5/6:ℝ)≤1-2*p*c by linarith)
      (by norm_num : (0:ℝ)≤5/6) (by linarith : 0≤1-p)
    norm_num at hh
    exact hh
  have hJhi : crossingDen ν p 2≤5/2 := by
    unfold crossingDen
    have hh : 0≤(5/6+ν)*p := by positivity
    nlinarith
  unfold crossingCut
  suffices ν/10≤ν*(1-p)*(1-2*p*c)/crossingDen ν p 2 by linarith
  apply (le_div_iff₀ hJ).mpr
  have hh := mul_le_mul_of_nonneg_left hU hν.le
  have hh' := mul_le_mul_of_nonneg_left hJhi (show 0≤ν/10 by positivity)
  nlinarith only [hh,hh',hν.le]

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

theorem cap_rate_zero {ν c : ℝ} (hν : ν≤3/4) :
    capCrossingRate c ν 0=unmarkedCountRate ν := by
  have hden : 15-6*ν≠0 := by linarith
  have hden2 : 15-ν*6≠0 := by nlinarith
  have hJid : crossingDen ν 0 2=(15-6*ν)/6 := by unfold crossingDen; ring
  unfold capCrossingRate crossingRate unmarkedCountRate
  rw [hJid]
  simp only [mul_zero,sub_zero,one_mul,mul_one,zero_mul]
  field_simp [hden,hden2]
  <;> ring

theorem rawRate_zero_ge_unmarked {B L c ν : ℝ} (hν : 0<ν) (hνhi : ν≤3/4) :
    unmarkedCountRate ν≤rawRepeatedCountRate B L c ν 0 := by
  have hp : (0:ℝ)/(2*ν)=0 := zero_div _
  unfold rawRepeatedCountRate
  rw [hp,← cap_rate_zero (c:=c) hνhi]
  exact (le_max_left _ _).trans (le_max_left _ _)

end
end Qrh.JointDetector.RepeatedMarks
