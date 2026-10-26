import Candidate.Cycle63.Physical.AllocationClipping
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import Candidate.Cycle63.Arithmetic.Window
import Candidate.Cycle63.Optimization.ChannelWindow
import Candidate.Cycle63.Arithmetic.FirstLevel

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

/-- The first plain factor of the comparison: the power of `Z` with the length of the comparison. -/
def comparisonFirstAt (Z Lc : ℝ) : ℝ := Z^Lc

/-- The second plain factor of the comparison: the product of the two plain factors over the first. -/
def comparisonSecondAt (Z Lc X₁ X₂ : ℝ) : ℝ := X₁*X₂/comparisonFirstAt Z Lc

theorem comparisonAt_positive (Z Lc X₁ X₂ : ℝ) (hZ : 0<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    0<comparisonFirstAt Z Lc ∧ 0<comparisonSecondAt Z Lc X₁ X₂ :=
  ⟨Real.rpow_pos_of_pos hZ _,div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos hZ _)⟩

theorem comparisonAt_same_product (Z Lc X₁ X₂ : ℝ) (hZ : 0<Z) :
    comparisonFirstAt Z Lc*comparisonSecondAt Z Lc X₁ X₂=X₁*X₂ := by
  unfold comparisonSecondAt
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hZ Lc).ne'

/-- The comparison of length `Lc` of plain factors of lengths `n₁` and `n₂` in a state of width `M` with slot
sum `slots` fits: its length lies in `[0, M/4]`, its second factor is at least half the width, the plain lengths
together are at most the width, and the reflected daughter fits in the old region with a margin of `M/100`. -/
def ComparisonFits (M Lc n₁ n₂ slots : ℝ) : Prop :=
  0≤Lc ∧ Lc≤M/4 ∧ M/2≤n₁+n₂-Lc ∧ n₁+n₂≤M ∧ M/100+2*Lc+(9/2)*slots≤n₁+n₂

/-- The comparison of the ledger fits for plain lengths and slots in the window of the ledger, at width one. -/
theorem comparisonFits_of_window {n₁ n₂ z : ℝ} (h : Cycle63.AffineLedger.PlainWindow n₁ n₂ z) (hz : 0≤z) :
    ComparisonFits 1 (Cycle63.AffineLedger.comparisonLength n₁ n₂ z) n₁ n₂ z := by
  have hvol := h.volume_le hz
  have h1 := Cycle63.AffineLedger.comparisonLength_nonneg n₁ n₂ z h
  have h2 := Cycle63.AffineLedger.comparisonLength_le n₁ n₂ z h
  have h3 := Cycle63.AffineLedger.long_factor n₁ n₂ z h
  have h4 := Cycle63.AffineLedger.daughter_fits n₁ n₂ z h
  exact ⟨h1,by linarith,by linarith,by linarith,by linarith⟩

/-- The second plain factor of the comparison of two powers of `Z` is the power with the sum of the lengths less
the length of the comparison. -/
theorem comparisonSecondAt_pow (Z Lc n₁ n₂ : ℝ) (hZ : 1<Z) :
    comparisonSecondAt Z Lc (Z^n₁) (Z^n₂)=Z^(n₁+n₂-Lc) := by
  unfold comparisonSecondAt comparisonFirstAt
  rw [←Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_sub (zero_lt_one.trans hZ)]

/-- The new parent's daughter has old capacity. No old capacity is imposed on that parent: the short factor
and the reflected long factor fit with the slots. -/
theorem reflected_daughter_capacity (Z width along bshort slots xi : ℝ)
    (hZ : 1<Z) (hbshort : 0≤bshort) (hxi : 0≤xi) (hup : along+bshort≤width)
    (hfit : bshort+xi+(9/2)*slots≤along) :
    max 0 (width-along+xi)+length Z (Z^bshort)+(9/2)*slots≤width := by
  rw [length_rpow Z bshort hZ,max_eq_right hbshort]
  rcases le_total 0 (width-along+xi) with h|h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

theorem length_le_of_scale_le (Z X R : ℝ) (hZ : 1<Z) (hR : 0≤R)
    (hX : X≤Z^R) : length Z X≤R := by
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left 1 X))
    (max_le (Real.one_le_rpow hZ.le hR) hX)
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

end
end OAI.SevenEighths.Cycle63FirstGeometry
