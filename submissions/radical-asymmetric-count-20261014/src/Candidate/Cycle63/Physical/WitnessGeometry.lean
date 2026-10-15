import Candidate.Cycle63.Arithmetic.Bernstein.Feedback
import Candidate.Cycle25.Assembly.Count.Crossing

namespace Cycle63.Physical

open Arithmetic Arithmetic.Bernstein

noncomputable section

def witnessCutoff (κ delta p : ℝ) : ℝ :=
  1 + delta * countingCoefficient κ p / (2 * rowDen κ delta p)

def rStar (κ p t : ℝ) : ℝ :=
  (2 * (1 - p / (3 * κ)) * t + p / (3 * κ) - p) /
    (3 - p - 2 * p / (3 * κ))

-- These predecessor results are variable-κ arithmetic, with no moment premise.
theorem rStar_eq_crossing (κ p t : ℝ) :
    rStar κ p t = OAI.SevenEighths.Cycle25DetectorRowCount.crossing p κ t := by
  unfold rStar OAI.SevenEighths.Cycle25DetectorRowCount.crossing
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator
    OAI.SevenEighths.Cycle25DetectorRowCount.b
  ring

theorem coefficient_eq_old {κ p : ℝ} (hk : 7 / 10 ≤ κ) :
    countingCoefficient κ p = OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p κ := by
  simpa only [OAI.SevenEighths.Cycle25DetectorRowCount.coefficient,
    OAI.SevenEighths.Cycle25DetectorRowCount.primeWeight,
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator,
    OAI.SevenEighths.Cycle25DetectorRowCount.b, mul_div_assoc] using
      canonical_counting_formula hk

theorem witnessCutoff_bounds {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    1 ≤ witnessCutoff κ delta p ∧ witnessCutoff κ delta p ≤ 3 / 2 := by
  have hc := countingCoefficient_pos hk hp
  have hden := rowDen_pos hk (show 0 ≤ delta ∧ delta ≤ 5 / 6 by constructor <;> linarith) hp
  have hdc := mul_nonneg hd.1 hc.le
  have hV : 0 ≤ 5 / 6 - delta := by linarith
  unfold witnessCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hdc (by linarith))
  · have hratio : delta * countingCoefficient κ p / (2 * rowDen κ delta p) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 2 * rowDen κ delta p)).mpr
      unfold rowDen
      linarith
    linarith

theorem witness_crossing_bounds {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    13 / 21 ≤ rStar κ p (witnessCutoff κ delta p) ∧
      rStar κ p (witnessCutoff κ delta p) ≤ 1 ∧
      1 / 3 ≤ witnessCutoff κ delta p - rStar κ p (witnessCutoff κ delta p) ∧
      witnessCutoff κ delta p - rStar κ p (witnessCutoff κ delta p) ≤ 1 / 2 := by
  have ht := witnessCutoff_bounds hk.1 hd hp
  rw [rStar_eq_crossing]
  have hr := OAI.SevenEighths.Cycle25DetectorRowCount.crossing_bounds
    hp.1 hp.2 hk.1 hk.2 ht.1 ht.2
  exact ⟨by linarith [hr.1], hr.2.1, hr.2.2⟩

theorem witness_envelope {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    1 - delta + delta * countingCoefficient κ p * (3 / 2 - witnessCutoff κ delta p) =
      countingR κ delta p ∧
    1 - delta + (5 / 6 - delta) * (witnessCutoff κ delta p - 1) =
      countingR κ delta p := by
  have hn := ne_of_gt (rowDen_pos hk
    (show 0 ≤ delta ∧ delta ≤ 5 / 6 by constructor <;> linarith) hp)
  unfold witnessCutoff countingR
  constructor
  · field_simp [hn]
    unfold rowDen
    ring
  · ring

theorem witness_crossing_identity {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    let t := witnessCutoff κ delta p
    let r := rStar κ p t
    (1 - delta * p - (delta - delta * p) * r = countingR κ delta p) ∧
    (1 - delta * p / (3 * κ) - 2 * (delta - delta * p / (3 * κ)) * (t - r) =
      countingR κ delta p) := by
  dsimp only
  have hD : OAI.SevenEighths.Cycle25DetectorRowCount.denominator p κ ≠ 0 := by
    have := OAI.SevenEighths.Cycle25DetectorRowCount.denominator_lower hp.1 hp.2 hk.1 hk.2
    linarith
  have henv := (witness_envelope hk.1 hd hp).1
  rw [coefficient_eq_old hk.1] at henv
  have hi := OAI.SevenEighths.Cycle25DetectorRowCount.inverse_at_crossing
    delta p κ (witnessCutoff κ delta p) hD
  have hplain := OAI.SevenEighths.Cycle25DetectorRowCount.plain_at_crossing
    delta p κ (witnessCutoff κ delta p) hD
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.inverseExponent
    OAI.SevenEighths.Cycle25DetectorRowCount.shortExponent at hi
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.plainExponent
    OAI.SevenEighths.Cycle25DetectorRowCount.shortExponent
    OAI.SevenEighths.Cycle25DetectorRowCount.b at hplain
  rw [rStar_eq_crossing]
  constructor
  · linarith
  · convert hplain.trans henv using 1
    ring

theorem witness_capacities {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    let t := witnessCutoff κ delta p
    let r := rStar κ p t
    (0 ≤ (1 - r) / 2 ∧ (1 - r) / 2 ≤ 4 / 21) ∧
    (0 ≤ (1 - 2 * (t - r)) / (6 * κ) ∧
      (1 - 2 * (t - r)) / (6 * κ) ≤ 1 / 12) := by
  dsimp only
  have hr := witness_crossing_bounds hk hd hp
  have hden : 0 < 6 * κ := by linarith [hk.1]
  refine ⟨⟨by linarith [hr.2.1], by linarith [hr.1]⟩, ?_, ?_⟩
  · exact div_nonneg (by linarith [hr.2.2.2]) hden.le
  · apply (div_le_iff₀ hden).mpr
    linarith [hr.2.2.1, hk.1]

theorem inverse_decrement_margins {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) (nu : ℝ) :
    let r := rStar κ p (witnessCutoff κ delta p)
    let z := (1 - r) / 2 - nu
    (1 - (r + 2 * z) = 2 * nu) ∧
    (3 - (2 * r + 8 * z) = 8 * nu + (2 * r - 1)) ∧
    8 * nu + 5 / 21 ≤ 3 - (2 * r + 8 * z) := by
  dsimp only
  have hr := (witness_crossing_bounds hk hd hp).1
  refine ⟨by ring, by ring, ?_⟩
  linarith

end

end Cycle63.Physical

#print axioms Cycle63.Physical.witness_crossing_bounds
#print axioms Cycle63.Physical.witness_envelope
#print axioms Cycle63.Physical.witness_crossing_identity
#print axioms Cycle63.Physical.witness_capacities
#print axioms Cycle63.Physical.inverse_decrement_margins
