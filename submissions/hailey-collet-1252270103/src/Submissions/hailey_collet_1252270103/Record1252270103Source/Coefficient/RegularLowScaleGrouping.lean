/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite common scale intervals preserve the two-coordinate affine sum.
Uses the original Cycle61 exponent bins, with their fixed, Z-independent count. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowActualCapacityAdmission
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondHighBins
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowScaleGrouping
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open CenteredMomentEnergyBands Cycle61InitialMass QRH.Record12518109Source

def coordinates (Z X₁ X₂ Q : ℝ) : Fin 3 → ℝ := ![length Z X₁,length Z X₂,Q]
def key (width Z X₁ X₂ Q : ℝ) : Fin 3 → ℤ := exponentBin width (coordinates Z X₁ X₂ Q)
def radial (width Mmax : ℝ) (k : Fin 3 → ℤ) : ℝ := min Mmax (exponentBinUpper width k 2)

theorem same_key_enclosure (width Z X₁ X₂ Q : ℝ) (hw : 0 < width)
    (k : Fin 3 → ℤ) (hk : key width Z X₁ X₂ Q = k) :
    length Z X₁ ≤ exponentBinUpper width k 0 ∧ exponentBinUpper width k 0 ≤ length Z X₁+width ∧
    length Z X₂ ≤ exponentBinUpper width k 1 ∧ exponentBinUpper width k 1 ≤ length Z X₂+width ∧
    Q ≤ exponentBinUpper width k 2 ∧ exponentBinUpper width k 2 ≤ Q+width := by
  change exponentBin width (coordinates Z X₁ X₂ Q) = k at hk
  have he (i : Fin 3) : coordinates Z X₁ X₂ Q i ≤ exponentBinUpper width k i ∧
      exponentBinUpper width k i ≤ coordinates Z X₁ X₂ Q i+width := by
    have hi := exponent_bin_enclosure width hw (coordinates Z X₁ X₂ Q) i
    rw [hk] at hi
    exact hi
  simpa [coordinates] using
    And.intro (he 0).1 (And.intro (he 0).2 (And.intro (he 1).1
      (And.intro (he 1).2 (And.intro (he 2).1 (he 2).2))))

/-- The common radial scale stays inside the source's exact closed interval,
even when a bin meets its upper endpoint. -/
theorem same_key_radial (width Z X₁ X₂ Q Mmin Mmax : ℝ) (hw : 0 < width)
    (k : Fin 3 → ℤ) (hk : key width Z X₁ X₂ Q = k)
    (hlo : Mmin ≤ Q) (hhi : Q ≤ Mmax) :
    Mmin ≤ radial width Mmax k ∧ radial width Mmax k ≤ Mmax ∧
      Q ≤ radial width Mmax k ∧ radial width Mmax k ≤ Q+width := by
  obtain ⟨_,_,_,_,h₁,h₂⟩ := same_key_enclosure width Z X₁ X₂ Q hw k hk
  have hQ : Q ≤ radial width Mmax k := le_min hhi h₁
  exact ⟨hlo.trans hQ,min_le_left _ _,hQ,(min_le_right _ _).trans h₂⟩

theorem raw_le_power_of_clipped_le (Z X u : ℝ) (hZ : 1 < Z)
    (hu : length Z X ≤ u) : X ≤ Z^u := by
  calc
    X ≤ max 1 X := le_max_right _ _
    _ = Z^(length Z X) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
      (zero_lt_one.trans_le (le_max_left _ _))).symm
    _ ≤ Z^u := Real.rpow_le_rpow_of_exponent_le hZ.le hu

theorem length_power (Z u : ℝ) (hZ : 1 < Z) (hu : 0 ≤ u) : length Z (Z^u) = u := by
  have hp : 1 ≤ Z^u := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ.le hu
  rw [length,max_eq_right hp,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

/-- Both envelopes come from this same row's interval key. Taking unrelated
coordinate maxima would not preserve the source's affine sum constraint. -/
theorem same_key_plain_envelopes (width Z X₁ X₂ Q : ℝ) (hw : 0 < width) (hZ : 1 < Z)
    (k : Fin 3 → ℤ) (hk : key width Z X₁ X₂ Q = k) :
    let u := exponentBinUpper width k
    0 ≤ u 0 ∧ 0 ≤ u 1 ∧
    X₁ ≤ Z^(u 0) ∧ X₂ ≤ Z^(u 1) ∧
    0 < Z^(u 0) ∧ 0 < Z^(u 1) ∧
    length Z (Z^(u 0)) = u 0 ∧ length Z (Z^(u 1)) = u 1 ∧
    u 0 + u 1 ≤ length Z X₁ + length Z X₂ + 2*width := by
  intro u
  obtain ⟨h₁,h₁',h₂,h₂',_,_⟩ := same_key_enclosure width Z X₁ X₂ Q hw k hk
  have hn₁ : 0 ≤ u 0 := (Real.logb_nonneg hZ (le_max_left 1 X₁)).trans h₁
  have hn₂ : 0 ≤ u 1 := (Real.logb_nonneg hZ (le_max_left 1 X₂)).trans h₂
  exact ⟨hn₁,hn₂,raw_le_power_of_clipped_le Z X₁ (u 0) hZ h₁,
    raw_le_power_of_clipped_le Z X₂ (u 1) hZ h₂,
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _,Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _,
    length_power Z (u 0) hZ hn₁,length_power Z (u 1) hZ hn₂,by linarith only [h₁',h₂']⟩

/-- Enlarging only the radial coordinate preserves a downward global face. -/
theorem face_radial_mono (B lam h n₁ n₂ slots Q M : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h) (hQM : Q ≤ M)
    (ha : (SourceFace.mk B lam 0 B 0 h).Admissible n₁ n₂ slots Q) :
    (SourceFace.mk B lam 0 B 0 h).Admissible n₁ n₂ slots M := by
  change 0*Q ≤ n₁ ∧ n₁ ≤ B*Q ∧ 0*Q ≤ n₂ ∧ n₂ ≤ B*Q ∧
    0*Q ≤ slots ∧ slots ≤ h*Q ∧ n₁+n₂+lam*slots ≤ B*Q at ha
  change 0*M ≤ n₁ ∧ n₁ ≤ B*M ∧ 0*M ≤ n₂ ∧ n₂ ≤ B*M ∧
    0*M ≤ slots ∧ slots ≤ h*M ∧ n₁+n₂+lam*slots ≤ B*M
  have hb := mul_le_mul_of_nonneg_left hQM hB
  have hs := mul_le_mul_of_nonneg_left hQM hh
  simpa only [zero_mul] using
    And.intro ha.1 (And.intro (ha.2.1.trans hb) (And.intro ha.2.2.1
      (And.intro (ha.2.2.2.1.trans hb) (And.intro ha.2.2.2.2.1
        (And.intro (ha.2.2.2.2.2.1.trans hs) (ha.2.2.2.2.2.2.trans hb))))))

/-- The geometric source admission may be applied before grouping. Each
nonempty fiber has common envelopes and a common allowed radial exponent. -/
theorem same_key_face_admission (width Z X₁ X₂ Q Mmin Mmax B lam h slots : ℝ)
    (hw : 0 < width) (hZ : 1 < Z) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (k : Fin 3 → ℤ) (hk : key width Z X₁ X₂ Q = k)
    (hlo : Mmin ≤ Q) (hhi : Q ≤ Mmax)
    (hadmit : ∀ n₁ n₂ : ℝ, 0 ≤ n₁ → 0 ≤ n₂ →
      n₁ ≤ length Z X₁+width → n₂ ≤ length Z X₂+width →
      (SourceFace.mk B lam 0 B 0 h).Admissible n₁ n₂ slots Q) :
    (SourceFace.mk B lam 0 B 0 h).Admissible
      (exponentBinUpper width k 0) (exponentBinUpper width k 1) slots (radial width Mmax k) := by
  have he := same_key_enclosure width Z X₁ X₂ Q hw k hk
  have hp := same_key_plain_envelopes width Z X₁ X₂ Q hw hZ k hk
  exact face_radial_mono B lam h _ _ slots Q _ hB hh
    (same_key_radial width Z X₁ X₂ Q Mmin Mmax hw k hk hlo hhi).2.2.1
    (hadmit _ _ hp.1 hp.2.1 he.2.1 he.2.2.2.1)

/-- The number of common scale intervals is fixed before Z and the row set. -/
theorem scale_keys_card {Row : Type*} (rows : Finset Row)
    (X₁ X₂ Q : Row → ℝ) (Z width bound : ℝ) (hw : 0 < width)
    (hbox : ∀ r ∈ rows, ∀ i, -bound ≤ coordinates Z (X₁ r) (X₂ r) (Q r) i ∧
      coordinates Z (X₁ r) (X₂ r) (Q r) i ≤ bound) :
    (rows.image (fun r => key width Z (X₁ r) (X₂ r) (Q r))).card ≤
      (Finset.Icc (⌊-bound/width⌋:ℤ) ⌊bound/width⌋).card^3 :=
  exponent_bins_card rows (fun r => coordinates Z (X₁ r) (X₂ r) (Q r)) width bound hw hbox

end
end QRH.Record1252270103Source.RegularLowScaleGrouping
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.same_key_enclosure
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.same_key_radial
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.raw_le_power_of_clipped_le
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.length_power
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.same_key_plain_envelopes
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.face_radial_mono
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.same_key_face_admission
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.scale_keys_card
