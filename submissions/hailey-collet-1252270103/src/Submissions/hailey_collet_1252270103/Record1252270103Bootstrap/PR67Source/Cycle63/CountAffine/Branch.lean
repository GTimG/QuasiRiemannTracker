import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.CountAffine.RegionFacts
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The detector-game case analysis with the affine plain branch (after tracker PR #52), with the
plain moment at its full slot capacity `zS m = min slotTop ((B - 2m)/λ)`: the plain line is the
larger of the affine line and the line with the capacity at the window top `slotTop`, so the count is
the larger of the two closed forms. Arithmetic only: every analytic branch bound is a hypothesis.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.CountAffine
noncomputable section
open Cycle63.Arithmetic

theorem promote_rpow {Bc C U p q : ℝ} (hC : 0 ≤ C) (hU : 1 ≤ U)
    (h : Bc ≤ C*U^p) (hpq : p ≤ q) : Bc ≤ C*U^q :=
  h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpq) hC)

theorem inverseLine_eq (δ x r : ℝ) : 1 - δ*(x + (1-x)*r) = inverseLine δ x r := by
  unfold inverseLine sI; ring

/-- The count for one plain line, at any cutoff `t` at least the line's balanced cutoff. -/
theorem line_count_bound (Bc C U δ x κ t r m ε ν γ a s tL rL mL RL : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hγs : γ ≤ crossingSlack)
    (F : LineFacts δ x a s tL rL mL RL) (htL : tL ≤ t)
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : Bc ≤ C*U^(max 1 ((1+5*r)/6) - δ*r + ε))
    (hP0 : Bc ≤ C*U^(1 - 2*δ*m + ε))
    (hI : inverseFloor ≤ r → r < 1 → ν < (1-r)/2 → Bc ≤ C*U^(1 - δ*(x + (1-x)*r) + ε))
    (hPo : plainTop < m → m < 1/2 → ν < (1-2*m)/(6*κ) → Bc ≤ C*U^(plainOld κ δ x m + ε))
    (hPL : windowBottom ≤ m → m ≤ plainTop → Bc ≤ C*U^(a - s*m + 2*ν + ε)) :
    Bc ≤ C*U^(max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ) := by
  have hsI : 0 ≤ sI δ x := sI_nonneg hδ (by linarith)
  have hsI1 : sI δ x ≤ 1 := by unfold sI; nlinarith
  have hv : 0 ≤ 5/6-δ := by linarith
  have hRt : RL ≤ 1/6 + (5/6-δ)*t := by
    rw [F.closed]; nlinarith [mul_le_mul_of_nonneg_left htL hv]
  have hR0 : 1 - δ ≤ RL := by
    have := F.tlo
    unfold cutoffFloor inverseFloor windowBottom crossingSlack at this
    rw [F.closed]; nlinarith
  have hLm := le_max_left (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop)
  have hOm := le_max_right (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop)
  let target := max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
  have promote := fun (p : ℝ) (h : Bc ≤ C*U^p) (hp : p ≤ target) => promote_rpow hC hU h hp
  -- Long inverse witness.
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1+5*r)/6) = (1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hm := mul_le_mul_of_nonneg_left hright hv
    show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
    nlinarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax1 : max 1 ((1+5*r)/6) = 1 := max_eq_left (by linarith)
  rw [hmax1] at hI0
  have hzeroI : (1-r)/2 ≤ ν → Bc ≤ C*U^target := by
    intro hcap
    apply promote _ hI0
    have : δ*r ≥ δ*(1-2*ν) := mul_le_mul_of_nonneg_left (by linarith) hδ
    show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
    nlinarith
  by_cases hmhalf : 1/2 ≤ m
  · apply promote _ hP0
    have := mul_le_mul_of_nonneg_left hmhalf hδ
    show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
    linarith
  have hmhalf' : m < 1/2 := lt_of_not_ge hmhalf
  by_cases hmtop : plainTop < m
  · by_cases hcap : (1-2*m)/(6*κ) ≤ ν
    · apply promote _ hP0
      have hk0 : 0 < 6*κ := by linarith
      have h1 : 1-2*m ≤ 6*κ*ν := (div_le_iff₀ hk0).mp hcap |>.trans_eq (by ring)
      have h2 : δ*(1-2*m) ≤ δ*(6*κ*ν) := mul_le_mul_of_nonneg_left h1 hδ
      have h3 : δ*(6*κ*ν) ≤ 6*ν := by nlinarith
      show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
      nlinarith
    · apply promote _ (hPo hmtop hmhalf' (lt_of_not_ge hcap))
      have hmono := plainOld_anti (κ := κ) (δ := δ) (p := x) hk hδ hx hx' hmtop.le
      show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
      linarith
  have hmtop' : m ≤ plainTop := le_of_not_gt hmtop
  by_cases hmlow : m < windowBottom
  · have hr : inverseFloor ≤ r := by
      have := F.tlo; unfold cutoffFloor at this; linarith
    by_cases hcap : (1-r)/2 ≤ ν
    · exact hzeroI hcap
    · apply promote _ (hI hr hr1' (lt_of_not_ge hcap))
      rw [inverseLine_eq]
      have hmono := inverseLine_anti (δ := δ) (p := x) (r := tL - windowBottom - γ) (r' := r) hsI
        (by linarith)
      have hshift : inverseLine δ x (tL - windowBottom - γ) =
          inverseLine δ x (tL - windowBottom) + sI δ x*γ := by
        unfold inverseLine; ring
      have hsg : sI δ x*γ ≤ γ := mul_le_of_le_one_left hγ hsI1
      show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
      linarith [F.b3]
  have hmlow' : windowBottom ≤ m := le_of_not_gt hmlow
  by_cases hmc : mL ≤ m
  · apply promote _ (hPL hmlow' hmtop')
    have hmono : a - s*m ≤ a - s*mL := by nlinarith [F.slope]
    show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
    linarith [F.plain]
  · have hmc' : m < mL := lt_of_not_ge hmc
    have hrc : rL - γ ≤ r := by linarith [F.split]
    have hr : inverseFloor ≤ r := by
      have := F.rc; unfold crossingFloor at this; linarith
    by_cases hcap : (1-r)/2 ≤ ν
    · exact hzeroI hcap
    · apply promote _ (hI hr hr1' (lt_of_not_ge hcap))
      rw [inverseLine_eq]
      have hmono := inverseLine_anti (δ := δ) (p := x) hsI hrc
      have hshift : inverseLine δ x (rL - γ) = inverseLine δ x rL + sI δ x*γ := by
        unfold inverseLine; ring
      have hsg : sI δ x*γ ≤ γ := mul_le_of_le_one_left hγ hsI1
      show _ ≤ max (1/6 + (5/6-δ)*t) (plainOld κ δ x plainTop) + ε + 6*ν + 5*γ
      linarith [F.inverse]

/-- With the slot capacity `zS m`, the plain exponent is the affine line or the capped line. -/
theorem plainNew_cases (δ x m : ℝ) :
    ((B - 2*m)/lambda ≤ Cycle63.Optimization.slotTop ∧ plainNew δ x m = 1 - 2*(δ*x)*B/lambda - (2*δ - 4*(δ*x)/lambda)*m) ∨
      (Cycle63.Optimization.slotTop < (B - 2*m)/lambda ∧ plainNew δ x m = aPc δ x - sPc δ*m) := by
  rcases le_or_gt ((B - 2*m)/lambda) Cycle63.Optimization.slotTop with h | h
  · left
    refine ⟨h, ?_⟩
    unfold plainNew zS
    rw [min_eq_right h]
    have hl : lambda ≠ 0 := lambda_pos.ne'
    field_simp
    ring
  · right
    refine ⟨h, ?_⟩
    unfold plainNew zS aPc sPc
    rw [min_eq_left h.le]
    ring

/-- The count with both plain lines: at the cutoff `max (tStar) (tStarC)` the count exponent is
at most the new branch, the larger of the two closed forms or the old plain moment above the
window. -/
theorem merged_count_bound (Bc C U δ x κ t r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hγs : γ ≤ crossingSlack)
    (FA : LineFacts δ x (aP δ x) (sP δ x) (tStar δ x) (rC δ x) (mC δ x) (RStar δ x))
    (FC : LineFacts δ x (aPc δ x) (sPc δ) (tStarC δ x) (rCC δ x) (mCC δ x) (RStarC δ x))
    (ht : t = max (tStar δ x) (tStarC δ x))
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : Bc ≤ C*U^(max 1 ((1+5*r)/6) - δ*r + ε))
    (hP0 : Bc ≤ C*U^(1 - 2*δ*m + ε))
    (hI : inverseFloor ≤ r → r < 1 → ν < (1-r)/2 → Bc ≤ C*U^(1 - δ*(x + (1-x)*r) + ε))
    (hPo : plainTop < m → m < 1/2 → ν < (1-2*m)/(6*κ) → Bc ≤ C*U^(plainOld κ δ x m + ε))
    (hPn : windowBottom ≤ m → m ≤ plainTop → Bc ≤ C*U^(plainNew δ x m + 2*ν + ε)) :
    Bc ≤ C*U^(newBranch κ δ x + ε + 6*ν + 5*γ) := by
  have hv : 0 ≤ 5/6-δ := by linarith
  have hlong : 1/6 + (5/6-δ)*t = max (RStar δ x) (RStarC δ x) := by
    rw [ht, FA.closed, FC.closed]
    rcases le_total (tStar δ x) (tStarC δ x) with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left h hv])]
    · rw [max_eq_left h, max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left h hv])]
  unfold newBranch
  rw [← hlong]
  rcases plainNew_cases δ x m with ⟨_, hpl⟩ | ⟨_, hpl⟩
  · refine line_count_bound Bc C U δ x κ t r m ε ν γ (aP δ x) (sP δ x) (tStar δ x) (rC δ x)
      (mC δ x) (RStar δ x) hC hU hδ hδ' hx hx' hk hk1 hν hγ hγs FA (ht ▸ le_max_left _ _)
      hleft hright hI0 hP0 hI hPo ?_
    intro h1 h2
    have := hPn h1 h2
    rw [hpl] at this
    unfold aP sP
    convert this using 2
  · refine line_count_bound Bc C U δ x κ t r m ε ν γ (aPc δ x) (sPc δ) (tStarC δ x) (rCC δ x)
      (mCC δ x) (RStarC δ x) hC hU hδ hδ' hx hx' hk hk1 hν hγ hγs FC (ht ▸ le_max_right _ _)
      hleft hright hI0 hP0 hI hPo ?_
    intro h1 h2
    have := hPn h1 h2
    rwa [hpl] at this

end
end Cycle63.CountAffine

end Record1252270103Bootstrap.PR67
