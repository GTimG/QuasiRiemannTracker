/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   An actual finite left-radius bank and its source capacity loss. -/
import Candidate.C092.transport.LowActualFiniteCover

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

/-- A finite bank at actual radii inside the closed interval. Every live
radius is rounded downward by less than the chosen positive collar. -/
theorem finite_left_radius_bank {a b δ : ℝ} (_hab : a ≤ b) (hδ : 0 < δ) :
    ∃ bank : Finset ℝ, (∀ r ∈ bank, a ≤ r ∧ r ≤ b) ∧
      ∀ V : ℝ, a ≤ V → V ≤ b → ∃ r ∈ bank, r ≤ V ∧ V-r < δ := by
  let bank := ((Finset.range (Nat.floor ((b-a)/δ)+1)).image
    (fun k : ℕ => a+(k : ℝ)*δ)).filter (fun r => r ≤ b)
  refine ⟨bank,?_,?_⟩
  · intro r hr
    obtain ⟨hr,hb⟩ := Finset.mem_filter.mp hr
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hδ.le),hb⟩
  · intro V haV hVb
    let k := Nat.floor ((V-a)/δ)
    have hk : k < Nat.floor ((b-a)/δ)+1 := Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le))
    have hklo := Nat.floor_le (div_nonneg (sub_nonneg.mpr haV) hδ.le)
    have hkhi := Nat.lt_floor_add_one ((V-a)/δ)
    have hrV : a+(k : ℝ)*δ ≤ V := by
      have hh := (le_div_iff₀ hδ).1 hklo
      dsimp [k]
      linarith
    refine ⟨a+(k : ℝ)*δ,?_,hrV,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,rfl⟩,hrV.trans hVb⟩
    · have hh := (div_lt_iff₀ hδ).1 hkhi
      dsimp [k]
      linarith

/-- The literal source/native capacity for the original two ordinary caps. -/
def radiusWidth (n y V : ℝ) : ℝ :=
  (1-n/V-y/V)/2+continuedGain (y/V)

/-- This identity uses the original absolute caps, not fictitious enlarged
ordinary scales. -/
theorem radiusWidth_identity {n y V : ℝ} (hV : 0 < V) :
    V*radiusWidth n y V = (V-n-y)/2+V*continuedGain (y/V) := by
  unfold radiusWidth
  field_simp

/-- The actual source/native transition is favorable. The already checked
quarter secant gives a uniform coarse loss between any two source radii. -/
theorem two_radius_capacity_loss {n y r V : ℝ}
    (hy : sourceY0 ≤ y) (hr : 0 < r) (hrV : r ≤ V) (hVH : V ≤ (H : ℝ)) :
    V*radiusWidth n y V-r*radiusWidth n y r ≤ (3/4 : ℝ)*(V-r) := by
  let m := y/V
  let w := y/r
  have hV : 0 < V := hr.trans_le hrV
  have hypos : 0 ≤ y := source_domain.1.le.trans hy
  have hV1 : V ≤ 1 := hVH.trans H_real_bounds.2.le
  have hym : y ≤ m := (le_div_iff₀ hV).2 (mul_le_of_le_one_right hypos hV1)
  have hm0 : sourceY0 ≤ m := hy.trans hym
  have hmw : m ≤ w := by
    apply (div_le_div_iff₀ hV hr).2
    nlinarith [mul_nonneg hypos (sub_nonneg.mpr hrV)]
  have hmabs : V*m = y := by dsimp [m]; field_simp
  have hwabs : r*w = y := by dsimp [w]; field_simp
  have hδ : 0 ≤ V-r := sub_nonneg.mpr hrV
  rw [radiusWidth_identity hV,radiusWidth_identity hr]
  change (V-n-y)/2+V*continuedGain m-((r-n-y)/2+r*continuedGain w) ≤ _
  by_cases hmY : m ≤ sourceY
  · rw [continuedGain,ite_eq_left hmY]
    by_cases hwY : w ≤ sourceY
    · rw [continuedGain,ite_eq_left hwY]
      have hsec := sourceGain_quarter_secant hm0 hmw hwY
      have hsecR := mul_le_mul_of_nonneg_left hsec hr.le
      have hg := sourceGain_le_cent hm0 hmY
      have hgδ := mul_le_mul_of_nonneg_left hg hδ
      have hmHalf : m ≤ 1/2 := hmY.trans (by norm_num [sourceY])
      have hmδ := mul_le_mul_of_nonneg_left hmHalf hδ
      nlinarith
    · rw [continuedGain,ite_eq_right hwY]
      have hrY : r*sourceY < y := by
        have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hwY) hr
        linarith
      have hsec := sourceGain_quarter_secant hm0 hmY (le_refl sourceY)
      rw [source_native_value] at hsec
      have hsecV := mul_le_mul_of_nonneg_left hsec hV.le
      have hY : sourceY < 1 := by norm_num [sourceY]
      nlinarith [mul_nonneg hδ (show 0 ≤ 1-sourceY by linarith)]
  · have hwY : ¬w ≤ sourceY := fun h => hmY (hmw.trans h)
    rw [continuedGain,ite_eq_right hmY,continuedGain,ite_eq_right hwY]
    linarith

/-- A downward-rounded bank radius has larger labelled caps and its frozen
positive retained width loses at most the explicit collar and decrement. -/
theorem bank_capacity_loss {n y r V decrement : ℝ}
    (hy : sourceY0 ≤ y) (hr : 0 < r) (hrV : r ≤ V) (hVH : V ≤ (H : ℝ))
    (hwidth : 0 ≤ radiusWidth n y r) :
    V*radiusWidth n y V-V*(radiusWidth n y r-decrement) ≤
      (3/4 : ℝ)*(V-r)+V*decrement := by
  have h := two_radius_capacity_loss (n := n) hy hr hrV hVH
  have hmono := mul_le_mul_of_nonneg_right hrV hwidth
  nlinarith

end
end QRH.Cycle092.LowActual
