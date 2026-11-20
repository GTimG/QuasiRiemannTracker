/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic

/-!
# Appendix P.6 / Q.2: reduction of the mixed witness price to its crossover

The literal three-face penalty in (P14) is minimized, after adding the source
price, at the crossing of its constant and first rising faces. The source
function is abstract: monotonicity and its one-sided slope bound are explicit
hypotheses. This file does not assert those hypotheses for an unchecked
certificate interval.
-/

namespace QRH.Cycle090

noncomputable section

/-- The sign-dependent coefficient `k_sign` in (P14). -/
def witnessSignedCoefficient (kLower kUpper Δ : ℝ) : ℝ :=
  if Δ < 0 then kUpper else kLower

/-- The three genuine count-deficit faces of the mixed witness price in (P14). -/
def witnessPenalty (kLower kUpper F H M z : ℝ) : ℝ :=
  max F (witnessSignedCoefficient kLower kUpper (z - M) * (z - M) +
    max H (2 * kLower * max 0 (z - M)))

/-- The crossover between the constant deficit face and the first rising face. -/
def witnessCrossover (kUpper F H M : ℝ) : ℝ := M + (F - H) / kUpper

/-- The full scalar mixed price, with the source gain and all fixed fees retained. -/
def witnessPrice (b : ℝ → ℝ) (f fee kLower kUpper F H M z : ℝ) : ℝ :=
  f * b z + witnessPenalty kLower kUpper F H M z / 2 - fee

/-- The directed signs in (P14) place the crossover on the nonpositive-offset arm. -/
theorem witnessCrossover_le {kUpper F H M : ℝ}
    (hk : 0 < kUpper) (hF : F ≤ 0) (hH : 0 ≤ H) :
    witnessCrossover kUpper F H M ≤ M := by
  have hquot : (F - H) / kUpper ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hk)
  unfold witnessCrossover
  linarith

/-- The positive ordinary deficit face vanishes at the crossover. -/
theorem witnessCrossover_positivePart_eq_zero {kUpper F H M : ℝ}
    (hk : 0 < kUpper) (hF : F ≤ 0) (hH : 0 ≤ H) :
    max 0 (witnessCrossover kUpper F H M - M) = 0 := by
  exact max_eq_left (sub_nonpos.mpr (witnessCrossover_le hk hF hH))

/-- The signed linear term agrees with its upper coefficient at nonpositive offsets. -/
theorem witnessSignedCoefficient_mul_of_nonpos {kLower kUpper Δ : ℝ}
    (hΔ : Δ ≤ 0) :
    witnessSignedCoefficient kLower kUpper Δ * Δ = kUpper * Δ := by
  by_cases hlt : Δ < 0
  · simp [witnessSignedCoefficient, hlt]
  · have hzero : Δ = 0 := le_antisymm hΔ (le_of_not_gt hlt)
    simp [hzero, witnessSignedCoefficient]

/-- The two active affine faces have the same exact value at the crossover. -/
theorem witnessCrossover_face_eq {kUpper F H M : ℝ} (hk : kUpper ≠ 0) :
    kUpper * (witnessCrossover kUpper F H M - M) + H = F := by
  unfold witnessCrossover
  field_simp [hk]
  ring

/-- Substituting the finite-bank faces gives exactly Q.2's displayed crossover formula. -/
theorem witnessCrossover_bank_eq {kUpper density v ξ step ε mUpper : ℝ}
    (hk : kUpper ≠ 0) (hd : density ≠ 0) :
    witnessCrossover kUpper (-kUpper * (ξ + 3 * ε))
        ((v / density) * max 0 (ξ - step - 3 * ε)) (mUpper + ε) =
      mUpper + ε - ξ - 3 * ε -
        (v / (density * kUpper)) * max 0 (ξ - step - 3 * ε) := by
  unfold witnessCrossover
  field_simp [hk, hd]
  ring

/-- At the crossover the complete three-face penalty equals its constant face. -/
theorem witnessPenalty_at_crossover {kLower kUpper F H M : ℝ}
    (hk : 0 < kUpper) (hF : F ≤ 0) (hH : 0 ≤ H) :
    witnessPenalty kLower kUpper F H M (witnessCrossover kUpper F H M) = F := by
  unfold witnessPenalty
  rw [witnessCrossover_positivePart_eq_zero hk hF hH]
  simp only [mul_zero, max_eq_left hH]
  rw [witnessSignedCoefficient_mul_of_nonpos
    (sub_nonpos.mpr (witnessCrossover_le hk hF hH))]
  rw [witnessCrossover_face_eq (ne_of_gt hk), max_self]

/-- The full mixed price has the expected source-plus-constant value at the crossover. -/
theorem witnessPrice_at_crossover {b : ℝ → ℝ} {f fee kLower kUpper F H M : ℝ}
    (hk : 0 < kUpper) (hF : F ≤ 0) (hH : 0 ≤ H) :
    witnessPrice b f fee kLower kUpper F H M (witnessCrossover kUpper F H M) =
      f * b (witnessCrossover kUpper F H M) + F / 2 - fee := by
  unfold witnessPrice
  rw [witnessPenalty_at_crossover hk hF hH]

/-- Every witness penalty is bounded below by its constant face. -/
theorem witnessPenalty_ge_constant {kLower kUpper F H M z : ℝ} :
    F ≤ witnessPenalty kLower kUpper F H M z := by
  exact le_max_left _ _

/-- To the right of the crossover, the penalty grows at least with slope `kLower`. -/
theorem witnessPenalty_ge_rising_face {kLower kUpper F H M z : ℝ}
    (hk : 0 < kUpper) (hkOrder : kLower ≤ kUpper)
    (hF : F ≤ 0) (hH : 0 ≤ H)
    (hz : witnessCrossover kUpper F H M ≤ z) :
    F + kLower * (z - witnessCrossover kUpper F H M) ≤
      witnessPenalty kLower kUpper F H M z := by
  have hstar := witnessCrossover_le hk hF hH (M := M)
  have hface := witnessCrossover_face_eq (ne_of_gt hk) (F := F) (H := H) (M := M)
  have hinner : H ≤ max H (2 * kLower * max 0 (z - M)) := le_max_left _ _
  have houter :
      witnessSignedCoefficient kLower kUpper (z - M) * (z - M) +
          max H (2 * kLower * max 0 (z - M)) ≤
        witnessPenalty kLower kUpper F H M z := le_max_right _ _
  by_cases hleft : z - M < 0
  · have hcoeff : witnessSignedCoefficient kLower kUpper (z - M) = kUpper := by
      simp [witnessSignedCoefficient, hleft]
    rw [hcoeff] at houter
    have hslope := mul_le_mul_of_nonneg_right hkOrder (sub_nonneg.mpr hz)
    nlinarith
  · have hcoeff : witnessSignedCoefficient kLower kUpper (z - M) = kLower := by
      simp [witnessSignedCoefficient, hleft]
    rw [hcoeff] at houter
    have hslope := mul_le_mul_of_nonneg_right hkOrder (sub_nonneg.mpr hstar)
    nlinarith

/-- The crossover minimizes the complete price when the source decrease is paid by the face slope. -/
theorem witnessPrice_minimal_of_comparisons
    {b : ℝ → ℝ} {f fee L kLower kUpper F H M z : ℝ}
    (hf : 0 ≤ f) (hkLower : 0 < kLower) (hkOrder : kLower ≤ kUpper)
    (hF : F ≤ 0) (hH : 0 ≤ H) (hSlope : f * L ≤ kLower / 2)
    (hLeft : z ≤ witnessCrossover kUpper F H M →
      b (witnessCrossover kUpper F H M) ≤ b z)
    (hRight : witnessCrossover kUpper F H M ≤ z →
      b (witnessCrossover kUpper F H M) - L * (z - witnessCrossover kUpper F H M) ≤ b z) :
    witnessPrice b f fee kLower kUpper F H M (witnessCrossover kUpper F H M) ≤
      witnessPrice b f fee kLower kUpper F H M z := by
  have hkUpper : 0 < kUpper := lt_of_lt_of_le hkLower hkOrder
  rw [witnessPrice_at_crossover hkUpper hF hH]
  unfold witnessPrice
  rcases le_total z (witnessCrossover kUpper F H M) with hz | hz
  · have hb := mul_le_mul_of_nonneg_left (hLeft hz) hf
    have hp := witnessPenalty_ge_constant (kLower := kLower) (kUpper := kUpper)
      (F := F) (H := H) (M := M) (z := z)
    linarith
  · have hb := mul_le_mul_of_nonneg_left (hRight hz) hf
    have hp := witnessPenalty_ge_rising_face hkUpper hkOrder hF hH hz
    have hs := mul_le_mul_of_nonneg_right hSlope (sub_nonneg.mpr hz)
    nlinarith

/-- The P14 crossover reduction on any declared support, from monotonicity and a one-sided source bound. -/
theorem witnessPrice_minimal_on
    {support : Set ℝ} {b : ℝ → ℝ} {f fee L kLower kUpper F H M : ℝ}
    (hf : 0 ≤ f) (hkLower : 0 < kLower) (hkOrder : kLower ≤ kUpper)
    (hF : F ≤ 0) (hH : 0 ≤ H) (hSlope : f * L ≤ kLower / 2)
    (hMono : AntitoneOn b support)
    (hStar : witnessCrossover kUpper F H M ∈ support)
    (hSource : ∀ z ∈ support, witnessCrossover kUpper F H M ≤ z →
      b (witnessCrossover kUpper F H M) - L * (z - witnessCrossover kUpper F H M) ≤ b z) :
    ∀ z ∈ support,
      witnessPrice b f fee kLower kUpper F H M (witnessCrossover kUpper F H M) ≤
        witnessPrice b f fee kLower kUpper F H M z := by
  intro z hz
  apply witnessPrice_minimal_of_comparisons hf hkLower hkOrder hF hH hSlope
  · intro hleft
    exact hMono hz hStar hleft
  · exact hSource z hz

end

end QRH.Cycle090
