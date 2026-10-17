import Candidate.Target830.Parameters
import Candidate.Target830.Kernel.ClippedCapacityDamping
import Candidate.Cycle25.Numerator.BoxGeometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Target830.Physical

def plainScale (d t : ℝ) : ℝ := 1 - y / d + t
def affineCapacity (P : SourcePlane) (d t : ℝ) : ℝ :=
  (P.B - 2 * plainScale d t) / P.lambda
def shiftBase (d : ℝ) : ℝ := 2 * y / d - 1
def oldCapacity (b t : ℝ) : ℝ := max 0 ((b - 2 * t) / (9 / 2))
def zeroCapacity (P : SourcePlane) (d : ℝ) : ℝ :=
  min slotClip (affineCapacity P d 0)
def scheduledCapacity (P : SourcePlane) (d v : ℝ) : ℝ :=
  if v ≤ 2 * physicalSwitch then min slotClip (affineCapacity P d (v / 2))
  else oldCapacity (shiftBase d) (v / 2)
def dampingRate : ℝ := 1 / 1000

theorem physical_d_pos {d : ℝ} (hd : dMinus ≤ d) : 0 < d := by
  have hdm : 0 < dMinus := by norm_num [dMinus, h]
  linarith

theorem plainScale_exact_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ physicalSwitch) :
    499790 / 1193283 ≤ plainScale d t ∧
      plainScale d t ≤ 20153331986009 / 47821320006000 := by
  have hy : 0 ≤ y := by norm_num [y, h, ell, theta]
  have hdm : 0 < dMinus := by norm_num [dMinus, h]
  have hp := physical_d_pos hd.1
  have hhi := div_le_div_of_nonneg_left hy hdm hd.1
  have hlo := div_le_div_of_nonneg_left hy hp hd.2
  norm_num [y, h, ell, theta, dMinus, dPlus, physicalSwitch, plainScale] at *
  constructor <;> linarith

theorem plainScale_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ physicalSwitch) :
    plainLower < plainScale d t ∧ plainScale d t < 264 / 625 := by
  have hn := plainScale_exact_bounds hd ht
  norm_num [plainLower] at *
  constructor <;> linarith

theorem affineCapacity_bounds (P : SourcePlane) {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ physicalSwitch) :
    73 / 2000 < affineCapacity P d t ∧ affineCapacity P d t < 19 / 500 := by
  have hn := plainScale_exact_bounds hd ht
  cases P <;> norm_num [affineCapacity, SourcePlane.B, SourcePlane.lambda] <;>
    constructor <;> linarith

theorem affineCapacity_interior (P : SourcePlane) {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ physicalSwitch) :
    widthLower < affineCapacity P d t ∧ affineCapacity P d t < slotClip := by
  have hz := affineCapacity_bounds P hd ht
  norm_num [widthLower, slotClip] at *
  constructor <;> linarith

theorem affineCapacity_budget (P : SourcePlane) (d t : ℝ) :
    2 * plainScale d t + P.lambda * affineCapacity P d t = P.B := by
  have hp : P.lambda ≠ 0 := ne_of_gt (P.parameter_bounds.2.2.2.2.2.1)
  unfold affineCapacity
  field_simp
  ring

theorem affineCapacity_shift (P : SourcePlane) (d t : ℝ) :
    affineCapacity P d 0 - affineCapacity P d t = 2 * t / P.lambda := by
  unfold affineCapacity plainScale
  ring

theorem affine_shortening (P : SourcePlane) {d t n1 n2 z : ℝ}
    (h1 : n1 ≤ plainScale d t) (h2 : n2 ≤ plainScale d t)
    (hz : z ≤ affineCapacity P d t) : n1 + n2 + P.lambda * z ≤ P.B := by
  have hpos := P.parameter_bounds.2.2.2.2.2.1
  have hmul := mul_le_mul_of_nonneg_left hz hpos.le
  have hh := affineCapacity_budget P d t
  linarith

theorem small_slot_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ 264 / 625) (h2 : n2 ≤ 264 / 625)
    (hz : z ≤ widthLower) : n1 + n2 + (9 / 2) * z ≤ 1 - 11 / 5000 := by
  norm_num [widthLower] at hz
  linarith

theorem small_plain_shortening (P : SourcePlane) {n1 n2 n z : ℝ}
    (h1 : n1 ≤ plainLower) (h2 : n2 ≤ n)
    (hcone : 2 * n + P.lambda * z ≤ P.B) (hz : z ≤ widthUpper) :
    n1 + n2 + (9 / 2) * z ≤ 1 := by
  cases P <;> norm_num [plainLower, widthUpper, SourcePlane.lambda, SourcePlane.B] at * <;>
    linarith

theorem positive_supply {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    1 / 5 < ell / d := by
  have he : 0 ≤ ell := by norm_num [ell, theta]
  have hdpos := physical_d_pos hd.1
  have hh := div_le_div_of_nonneg_left he hdpos hd.2
  norm_num [ell, theta, dPlus, h] at hh ⊢
  linarith

theorem shiftBase_bounds {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    0 ≤ shiftBase d ∧ shiftBase d ≤ 1 / 6 := by
  have hy : 0 ≤ y := by norm_num [y, h, ell, theta]
  have hdm : 0 < dMinus := by norm_num [dMinus, h]
  have hhi := div_le_div_of_nonneg_left hy hdm hd.1
  have hlo := div_le_div_of_nonneg_left hy (physical_d_pos hd.1) hd.2
  have hhi' : y / d ≤ 693493 / 1193283 := by
    convert hhi using 1 <;> norm_num [y, h, ell, theta, dMinus]
  have hlo' : 13869860000 / 23910660003 ≤ y / d := by
    convert hlo using 1 <;> norm_num [y, h, ell, theta, dPlus]
  unfold shiftBase
  rw [mul_div_assoc]
  constructor <;> linarith

theorem scheduledCapacity_nonneg (P : SourcePlane) {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) :
    0 ≤ scheduledCapacity P d v := by
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hz := affineCapacity_interior P hd
      (show 0 ≤ v / 2 ∧ v / 2 ≤ physicalSwitch by constructor <;> linarith)
    apply le_min
    · norm_num [slotClip]
    · have : 0 ≤ widthLower := by norm_num [widthLower]
      linarith
  · exact le_max_left _ _

theorem scheduledCapacity_le_supply (P : SourcePlane) {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) :
    scheduledCapacity P d v ≤ ell / d := by
  have hs := positive_supply hd
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hh := min_le_left slotClip (affineCapacity P d (v / 2))
    have hc : slotClip < 1 / 5 := by norm_num [slotClip]
    exact hh.trans (hc.le.trans hs.le)
  · have hb := (shiftBase_bounds hd).2
    have hh : oldCapacity (shiftBase d) (v / 2) ≤ 1 / 25 := by
      unfold oldCapacity
      apply max_le
      · norm_num
      · linarith
    linarith

theorem zeroCapacity_eq_kernel (P : SourcePlane) (d : ℝ) :
    zeroCapacity P d = QRH830.ClippedCapacityDamping.baseCapacity
      P.lambda slotClip (1 - P.B) (shiftBase d) := by
  unfold zeroCapacity affineCapacity plainScale shiftBase
    QRH830.ClippedCapacityDamping.baseCapacity
  congr 1
  ring

theorem scheduledCapacity_eq_kernel (P : SourcePlane) (d v : ℝ) :
    scheduledCapacity P d v = QRH830.ClippedCapacityDamping.scheduledAt
      P.lambda slotClip (1 - P.B) (shiftBase d) physicalSwitch (v / 2) := by
  unfold scheduledCapacity QRH830.ClippedCapacityDamping.scheduledAt
  have hi : v ≤ 2 * physicalSwitch ↔ v / 2 ≤ physicalSwitch := by
    constructor <;> intro hh <;> linarith
  by_cases hs : v ≤ 2 * physicalSwitch
  · rw [ite_eq_left hs, ite_eq_left (hi.mp hs)]
    unfold affineCapacity plainScale shiftBase QRH830.ClippedCapacityDamping.shiftedCapacity
    congr 1
    ring
  · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hi.mpr h))]
    rfl

theorem scheduled_capacity_damping (P : SourcePlane) {d v a delta : ℝ}
    (_hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (had : a ≤ delta / 2) (hdelta : 0 ≤ delta) :
    a * zeroCapacity P d / 2 + dampingRate * delta * v ≤
      delta * v / 4 + a * scheduledCapacity P d v / 2 := by
  have hl : 2 ≤ P.lambda := by cases P <;> norm_num [SourcePlane.lambda]
  have hlarge : ∀ u : ℝ, physicalSwitch ≤ u → u / 500 ≤
      QRH830.ClippedCapacityDamping.reserve P.lambda slotClip (1 - P.B) (shiftBase d) u := by
    intro u hu
    cases P
    · simpa [SourcePlane.lambda, SourcePlane.B, physicalSwitch,
        QRH830.ClippedCapacityDamping.lamA, QRH830.ClippedCapacityDamping.BA,
        QRH830.ClippedCapacityDamping.switch] using
        QRH830.ClippedCapacityDamping.large_shift_A slotClip (shiftBase d) u
          (by norm_num [slotClip]) hu
    · simpa [SourcePlane.lambda, SourcePlane.B, physicalSwitch,
        QRH830.ClippedCapacityDamping.lamC, QRH830.ClippedCapacityDamping.BC,
        QRH830.ClippedCapacityDamping.switch] using
        QRH830.ClippedCapacityDamping.large_shift_C slotClip (shiftBase d) u
          (by norm_num [slotClip]) hu
  have hh := QRH830.ClippedCapacityDamping.scheduled_amplitude_damping
    P.lambda slotClip (1 - P.B) (shiftBase d) physicalSwitch (v / 2) a delta
    hl (by linarith) ha had hdelta hlarge
  rw [← zeroCapacity_eq_kernel P d, ← scheduledCapacity_eq_kernel P d v] at hh
  dsimp [dampingRate]
  convert hh using 1 <;> ring

theorem scaled_zeroCapacity (P : SourcePlane) {d : ℝ} (hd : 0 < d) :
    d * zeroCapacity P d =
      min (slotClip * d) ((2 * y - (2 - P.B) * d) / P.lambda) := by
  unfold zeroCapacity
  rw [mul_min_of_nonneg _ _ hd.le]
  congr 1
  · ring
  · unfold affineCapacity plainScale
    field_simp
    ring

theorem physical_y_range {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    1 / 2 ≤ y / d ∧ y / d < 1 := by
  have hb := (shiftBase_bounds hd).1
  have hp := physical_d_pos hd.1
  constructor
  · unfold shiftBase at hb
    rw [mul_div_assoc] at hb
    linarith
  · apply (div_lt_one hp).mpr
    have hh : y < dMinus := by norm_num [y, dMinus, h, ell, theta]
    exact hh.trans_le hd.1

theorem coefficient_box_geometry {d xi ann : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hxi : 0 < xi) (_hann : 0 ≤ ann)
    (hsmall : 2 * xi + ann ≤ 1 / 2) (j : ℕ)
    (hj : j ∈ Finset.range (Cycle25.Numerator.coefficientBoxCount xi + 1)) :
    0 ≤ 1 - y / d + (j : ℝ) * xi + xi ∧
      (1 - y / d + (j : ℝ) * xi + xi) + ann ≤ 2 := by
  have hy := physical_y_range hd
  have hv := Cycle25.Numerator.coefficient_box_index_range xi hxi j hj
  constructor <;> linarith

theorem scheduled_capacity_or_empty (P : SourcePlane) {α : Type*}
    (T : Finset α) (width : T → ℝ) {d t kap : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t) (hkap : kap ≤ 3 / 4)
    (hw : ∀ i, 0 < width i)
    (hselected : (∑ i, width i) ≤ scheduledCapacity P d (2 * t)) :
    (∃ d' t' : ℝ, dMinus ≤ d' ∧ d' ≤ dPlus ∧ 0 ≤ t' ∧ t' ≤ physicalSwitch ∧
      plainScale d t = plainScale d' t' ∧ (∑ i, width i) ≤ affineCapacity P d' t') ∨
      (2 * plainScale d t + 6 * kap * (∑ i, width i) ≤ 1 ∨ T = ∅) := by
  have hsum : 0 ≤ ∑ i, width i := Finset.sum_nonneg (fun i _ => (hw i).le)
  by_cases hsmall : t ≤ physicalSwitch
  · left
    refine ⟨d, t, hd.1, hd.2, ht, hsmall, rfl, ?_⟩
    have hh : (∑ i, width i) ≤ min slotClip (affineCapacity P d t) := by
      simpa [scheduledCapacity, show 2 * t ≤ 2 * physicalSwitch by linarith] using hselected
    exact hh.trans (min_le_right _ _)
  · right
    have hselected' : (∑ i, width i) ≤ oldCapacity (shiftBase d) t := by
      simpa [scheduledCapacity, show ¬ 2 * t ≤ 2 * physicalSwitch by linarith] using hselected
    by_cases hraw : 0 ≤ (shiftBase d - 2 * t) / (9 / 2)
    · left
      have hs : (∑ i, width i) ≤ (shiftBase d - 2 * t) / (9 / 2) := by
        simpa [oldCapacity, max_eq_right hraw] using hselected'
      have hbudget : 2 * plainScale d t + (9 / 2) * (∑ i, width i) ≤ 1 := by
        unfold plainScale shiftBase at *
        rw [mul_div_assoc] at hs
        linarith
      nlinarith
    · right
      have hs : (∑ i, width i) ≤ 0 := by
        simpa [oldCapacity, max_eq_left (le_of_not_ge hraw)] using hselected'
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hh := Finset.single_le_sum (fun (j : T) (_ : j ∈ Finset.univ) => (hw j).le)
        (Finset.mem_univ (⟨i, hi⟩ : T))
      linarith [hw ⟨i, hi⟩]

end OAI.SevenEighths.Target830.Physical

#print axioms OAI.SevenEighths.Target830.Physical.scheduled_capacity_damping
#print axioms OAI.SevenEighths.Target830.Physical.scaled_zeroCapacity
#print axioms OAI.SevenEighths.Target830.Physical.scheduled_capacity_or_empty
