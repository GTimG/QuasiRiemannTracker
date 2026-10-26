import Candidate.Cycle63.Physical.AllocationClipping
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow

namespace OAI.SevenEighths.Cycle63FirstGeometry
noncomputable section
set_option autoImplicit false
open HeckeFamily CenteredMomentEnergyBands CenteredMomentRetainedProfile
open CenteredMomentEnergyReferenceLowWindow

/-- Subunit raw lengths are clipped by the actual old moment definition. -/
theorem length_rpow (Z r : ℝ) (hZ : 1<Z) : length Z (Z^r)=max 0 r := by
  have hh := Cycle63.Physical.logb_clipped_scale Z (Z^r) hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r)
  simpa only [length,clippedScale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

/-- The new parent's daughter has old capacity. No old capacity is imposed on
that parent: only the .25/.5/.04 comparison geometry is used. -/
theorem reflected_daughter_capacity (Z M width along bshort slots xi : ℝ)
    (hZ : 1<Z) (hM : 0≤M) (hwidth : M≤width)
    (hlong : M/2≤along) (hshort : bshort≤M/4)
    (hslots : slots≤M/25) (hxi : 0≤xi) (hpadding : xi≤7*M/100) :
    max 0 (width-along+xi)+length Z (Z^bshort)+(9/2)*slots≤width := by
  rw [length_rpow Z bshort hZ]
  have hs : max 0 bshort≤M/4 := max_le (by linarith) hshort
  have hbound : max 0 (width-along+xi)≤width-M/2+xi :=
    max_le (by linarith) (by linarith)
  linarith

/-- Every retained annulus has the same actual old-capacity gate, including both
plain derivative choices; no individual annulus bound is assumed. -/
theorem reflected_window_capacity (Z M width along bshort slots xi v : ℝ)
    (hZ : 1<Z) (hM : 0≤M) (hwidth : M≤width)
    (hlong : M/2≤along) (hshort : bshort≤M/4)
    (hslots : slots≤M/25) (hxi : 0≤xi) (hpadding : xi≤7*M/100)
    (hv : v∈Set.Icc 0 (max 0 (width-along+xi)*Real.log Z)) :
    length Z (Real.exp v)+length Z (Z^bshort)+(9/2)*slots≤width := by
  have hh := (reflection_window_length Z (max 0 (width-along+xi)) v hZ
    (le_max_left _ _) hv).1
  have hc := reflected_daughter_capacity Z M width along bshort slots xi hZ hM hwidth
    hlong hshort hslots hxi hpadding
  linarith

theorem length_le_of_scale_le (Z X R : ℝ) (hZ : 1<Z) (hR : 0≤R)
    (hX : X≤Z^R) : length Z X≤R := by
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left 1 X))
    (max_le (Real.one_le_rpow hZ.le hR) hX)
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem direct_daughter_capacity (Z M width X₁ X₂ slots : ℝ)
    (hZ : 1<Z) (hM : 0≤M) (hwidth : M≤width)
    (hX₁ : X₁≤Z^(M/4)) (hX₂ : X₂≤Z^(M/2)) (hslots : slots≤M/25) :
    length Z X₁+length Z X₂+(9/2)*slots≤width := by
  have h₁ := length_le_of_scale_le Z X₁ (M/4) hZ (by linarith) hX₁
  have h₂ := length_le_of_scale_le Z X₂ (M/2) hZ (by linarith) hX₂
  linarith

/-- The literal equal-product comparison of the manuscript has second length
between .57M and .63M, hence belongs to the reflected public branch. -/
theorem actual_comparison_powers (Z M n₁ n₂ : ℝ) (hZ : 1<Z) (hM : 0≤M)
    (hn₁ : (41/100)*M≤n₁) (hn₂ : (41/100)*M≤n₂)
    (hn₁' : n₁≤(44/100)*M) (hn₂' : n₂≤(44/100)*M) :
    CenteredMomentEnergyReferenceState.comparisonSecond Z M (Z^n₁) (Z^n₂) =
      Z^(n₁+n₂-M/4) ∧ M/2≤n₁+n₂-M/4 ∧ n₁+n₂-M/4≤(63/100)*M := by
  refine ⟨?_,by linarith,by linarith⟩
  unfold CenteredMomentEnergyReferenceState.comparisonSecond
    CenteredMomentEnergyReferenceState.comparisonFirst
  rw [←Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_sub (zero_lt_one.trans hZ)]

end
end OAI.SevenEighths.Cycle63FirstGeometry
