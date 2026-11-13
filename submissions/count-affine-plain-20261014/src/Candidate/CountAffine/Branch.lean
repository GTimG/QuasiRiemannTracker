/- A48 (AI-assisted, for liqsweep): the detector-game case analysis with the affine plain branch.
Arithmetic only: every analytic branch bound is a hypothesis. Apache 2.0. -/
import Candidate.CountAffine.RegionFacts

set_option autoImplicit false

namespace Cycle61.CountAffine
noncomputable section

theorem promote_rpow {Bc C U p q : ℝ} (hC : 0 ≤ C) (hU : 1 ≤ U)
    (h : Bc ≤ C*U^p) (hpq : p ≤ q) : Bc ≤ C*U^q :=
  h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpq) hC)

theorem inverseLine_eq (δ x r : ℝ) : 1 - δ*(x + (1-x)*r) = inverseLine δ x r := by
  unfold inverseLine sI; ring

theorem RStar_le_newBranch (κ δ x : ℝ) : RStar δ x ≤ newBranch κ δ x := le_max_left _ _
theorem plainOld_le_newBranch (κ δ x : ℝ) : plainOld κ δ x plainTop ≤ newBranch κ δ x :=
  le_max_right _ _

/-- The four-branch count at the balanced cut-off `tStar`, on the closed-form region. -/
theorem affine_count_bound_of_branches (Bc C U δ x κ t r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hγs : γ ≤ 1/100)
    (hreg : inRegion δ x) (ht : t = tStar δ x)
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : Bc ≤ C*U^(max 1 ((1+5*r)/6) - δ*r + ε))
    (hP0 : Bc ≤ C*U^(1 - 2*δ*m + ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 → Bc ≤ C*U^(1 - δ*(x + (1-x)*r) + ε))
    (hPo : plainTop < m → m < 1/2 → ν < (1-2*m)/(6*κ) → Bc ≤ C*U^(plainOld κ δ x m + ε))
    (hPn : 41/100 ≤ m → m ≤ plainTop → Bc ≤ C*U^(plainNew δ x m + 2*ν + ε)) :
    Bc ≤ C*U^(newBranch κ δ x + ε + 6*ν + 5*γ) := by
  have F := facts_of_region hreg
  have hD := F.den
  have hS := F.sum
  obtain ⟨hcr1, hcr2⟩ := crossing_identities hD.ne' hS.ne'
  have hsI : 0 ≤ sI δ x := sI_nonneg hδ (by linarith)
  have hsI1 : sI δ x ≤ 1 := by unfold sI; nlinarith
  have htlo : 1927/1850 ≤ t := ht ▸ F.tlo
  have hR0 : 1 - δ ≤ RStar δ x := RStar_ge_base (by linarith) (by linarith [F.tlo])
  have hRN := RStar_le_newBranch κ δ x
  have hON := plainOld_le_newBranch κ δ x
  have hRdef : RStar δ x = 1/6 + (5/6-δ)*t := by rw [ht, RStar]
  let target := newBranch κ δ x + ε + 6*ν + 5*γ
  have promote := fun (p : ℝ) (h : Bc ≤ C*U^p) (hp : p ≤ target) => promote_rpow hC hU h hp
  -- Case A: long inverse witness.
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1+5*r)/6) = (1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hv : 0 ≤ 5/6-δ := by linarith
    have hm := mul_le_mul_of_nonneg_left hright hv
    show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
    nlinarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax1 : max 1 ((1+5*r)/6) = 1 := max_eq_left (by linarith)
  rw [hmax1] at hI0
  -- zero inverse capacity: the no-slot inverse bound suffices.
  have hzeroI : (1-r)/2 ≤ ν → Bc ≤ C*U^target := by
    intro hcap
    apply promote _ hI0
    have : δ*r ≥ δ*(1-2*ν) := mul_le_mul_of_nonneg_left (by linarith) hδ
    show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
    nlinarith
  by_cases hmhalf : 1/2 ≤ m
  · apply promote _ hP0
    have := mul_le_mul_of_nonneg_left hmhalf hδ
    show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
    linarith
  have hmhalf' : m < 1/2 := lt_of_not_ge hmhalf
  by_cases hmtop : plainTop < m
  · -- above the affine window: old plain moment, monotone down to the window edge.
    by_cases hcap : (1-2*m)/(6*κ) ≤ ν
    · apply promote _ hP0
      have hk0 : 0 < 6*κ := by linarith
      have h1 : 1-2*m ≤ 6*κ*ν := (div_le_iff₀ hk0).mp hcap |>.trans_eq (by ring)
      have h2 : δ*(1-2*m) ≤ δ*(6*κ*ν) := mul_le_mul_of_nonneg_left h1 hδ
      have h3 : δ*(6*κ*ν) ≤ 6*ν := by nlinarith
      show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
      nlinarith
    · apply promote _ (hPo hmtop hmhalf' (lt_of_not_ge hcap))
      have hmono := plainOld_anti (κ := κ) (δ := δ) (p := x) hk hδ hx hx' hmtop.le
      show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
      linarith
  have hmtop' : m ≤ plainTop := le_of_not_gt hmtop
  by_cases hmlow : m < 41/100
  · -- below the affine window: the inverse witness is long enough.
    have hr : 23/37 ≤ r := by linarith
    by_cases hcap : (1-r)/2 ≤ ν
    · exact hzeroI hcap
    · apply promote _ (hI hr hr1' (lt_of_not_ge hcap))
      rw [inverseLine_eq]
      have hmono := inverseLine_anti (δ := δ) (p := x) (r := t - 41/100 - γ) (r' := r) hsI (by linarith)
      have hb3 := F.b3
      rw [← ht] at hb3
      have hshift : inverseLine δ x (t - 41/100 - γ) = inverseLine δ x (t - 41/100) + sI δ x*γ := by
        unfold inverseLine; ring
      have hsg : sI δ x*γ ≤ γ := mul_le_of_le_one_left hγ hsI1
      show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
      linarith
  have hmlow' : 41/100 ≤ m := le_of_not_gt hmlow
  by_cases hmc : mC δ x ≤ m
  · -- affine plain branch beyond the crossing.
    apply promote _ (hPn hmlow' hmtop')
    have hmono := plainNew_anti (δ := δ) (p := x) hδ hx hx' hmc
    have hat := plainNew_at_crossing hD.ne' hS.ne' F.cap
    show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
    linarith
  · -- inverse branch before the crossing.
    have hmc' : m < mC δ x := lt_of_not_ge hmc
    have hrc : rC δ x - γ ≤ r := by
      have : rC δ x = t - mC δ x := by rw [ht, rC]
      linarith
    have hr : 23/37 ≤ r := by linarith [F.rc]
    by_cases hcap : (1-r)/2 ≤ ν
    · exact hzeroI hcap
    · apply promote _ (hI hr hr1' (lt_of_not_ge hcap))
      rw [inverseLine_eq]
      have hmono := inverseLine_anti (δ := δ) (p := x) hsI hrc
      have hshift : inverseLine δ x (rC δ x - γ) = inverseLine δ x (rC δ x) + sI δ x*γ := by
        unfold inverseLine; ring
      have hsg : sI δ x*γ ≤ γ := mul_le_of_le_one_left hγ hsI1
      show _ ≤ newBranch κ δ x + ε + 6*ν + 5*γ
      linarith

end
end Cycle61.CountAffine
