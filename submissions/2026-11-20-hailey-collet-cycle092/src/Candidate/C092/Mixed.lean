/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.MixedWitness
import Candidate.C092.Intake.QRH.SourceEnvelope
import Candidate.C092.Intake.QRH.ContactReceipt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Candidate.C092.Physical
import Candidate.C092.transport.TopData

/-! The authentic Q.2 source price, on its tested width corridor.
The final crossover theorem discharges the abstract monotonicity and slope
premises of `witnessPrice_minimal_on` for the actual receipt coefficients and
the actual joined polynomial source. Stored physical leaf margins are not
interpreted as price bounds here. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace QRH.Cycle092.Mixed
open QRH.Cycle090 QRH.ContactCertificate
noncomputable section

def widthLo : ℝ := 4643/12500
def widthHi : ℝ := 947/2500
def betaSlope : ℝ := (g1Receipt.lo : ℝ)
def betaIntercept : ℝ := (g0Receipt.hi : ℝ)/2
def beta (z : ℝ) : ℝ := betaSlope*z-betaIntercept+sourceGain z
def upperBeta (z : ℝ) : ℝ := betaSlope*z-betaIntercept+upperGain z
def lowerBeta (z : ℝ) : ℝ := betaSlope*z-betaIntercept+lowerGain z

theorem receipt_slope_bounds : 0 < betaSlope ∧ betaSlope < 19/250 := by
  norm_num [betaSlope,g1Receipt]

theorem width_corridor : sourceY0 < widthLo ∧ widthLo < sourceSeam ∧
    sourceSeam < widthHi ∧ widthHi < sourceY := by
  norm_num [widthLo,widthHi,sourceY0,sourceY,sourceSeam]

theorem upperBeta_hasDerivAt (z : ℝ) :
    HasDerivAt upperBeta (betaSlope+upperGainSlope z) z := by
  unfold upperBeta
  convert (((hasDerivAt_id z).const_mul betaSlope).sub_const betaIntercept).add
    (upperGain_hasDerivAt z) using 1 <;> first | rfl | simp

theorem lowerBeta_hasDerivAt (z : ℝ) :
    HasDerivAt lowerBeta (betaSlope+lowerGainSlope z) z := by
  unfold lowerBeta
  convert (((hasDerivAt_id z).const_mul betaSlope).sub_const betaIntercept).add
    (lowerGain_hasDerivAt z) using 1 <;> first | rfl | simp

/-- Exact derivative guards for the actual cubic price, rather than a supplied
derivative bound on an abstract source function. -/
theorem upperBeta_slope_bounds {z : ℝ} (hz₀ : sourceSeam ≤ z) (hz₁ : z ≤ widthHi) :
    -(1/4 : ℝ) < betaSlope+upperGainSlope z ∧ betaSlope+upperGainSlope z < 0 := by
  have hY := hz₁.trans width_corridor.2.2.2.le
  have hb := upperGain_slope_bounds hz₀ hY
  have ht : 1/100 ≤ sourceY-z := by norm_num [sourceY,widthHi] at hz₁ ⊢; linarith
  have ha := receipt_slope_bounds
  constructor
  · linarith
  · unfold upperGainSlope
    nlinarith [sq_nonneg (sourceY-z)]

/-- The lower polynomial price has the same strict derivative bounds. -/
theorem lowerBeta_slope_bounds {z : ℝ} (hz₀ : widthLo ≤ z) (hz₁ : z ≤ sourceSeam) :
    -(1/4 : ℝ) < betaSlope+lowerGainSlope z ∧ betaSlope+lowerGainSlope z < 0 := by
  have hb := lowerGain_slope_bounds (width_corridor.1.le.trans hz₀) hz₁
  have ha := receipt_slope_bounds
  constructor
  · linarith
  · have ht : 0 ≤ sourceSeam-z := sub_nonneg.mpr hz₁
    unfold lowerGainSlope
    nlinarith

/-- The source price is continuous at its true seam; its derivative has the
genuine downward jump recorded by the source, so no smoothness at the seam is assumed. -/
theorem beta_seam_join : lowerBeta sourceSeam = upperBeta sourceSeam := by
  simp only [lowerBeta,upperBeta,source_seam_join]

theorem beta_upper {z : ℝ} (hz : sourceSeam ≤ z) : beta z = upperBeta z := by
  simp [beta,upperBeta,sourceGain,hz]

theorem beta_lower {z : ℝ} (hz : z ≤ sourceSeam) : beta z = lowerBeta z := by
  by_cases he : sourceSeam ≤ z
  · have h := le_antisymm hz he
    subst z
    rw [beta_upper le_rfl, beta_seam_join]
  · simp [beta,lowerBeta,sourceGain,he]

theorem beta_hasDerivAt_upper {z : ℝ} (hz : sourceSeam < z) :
    HasDerivAt beta (betaSlope+upperGainSlope z) z := by
  apply (upperBeta_hasDerivAt z).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hz] with y hy
  exact beta_upper hy.le

theorem beta_hasDerivAt_lower {z : ℝ} (hz : z < sourceSeam) :
    HasDerivAt beta (betaSlope+lowerGainSlope z) z := by
  apply (lowerBeta_hasDerivAt z).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hz] with y hy
  exact beta_lower hy.le

theorem upperBeta_comparison {a b : ℝ}
    (ha : sourceSeam ≤ a) (hab : a ≤ b) (hb : b ≤ widthHi) :
    upperBeta b ≤ upperBeta a ∧ upperBeta a-(b-a)/4 ≤ upperBeta b := by
  have hc : ContinuousOn upperBeta (Set.Icc sourceSeam widthHi) := by
    unfold upperBeta upperGain; fun_prop
  have hd : DifferentiableOn ℝ upperBeta (interior (Set.Icc sourceSeam widthHi)) :=
    fun z _ => (upperBeta_hasDerivAt z).differentiableAt.differentiableWithinAt
  have hu : ∀ z ∈ interior (Set.Icc sourceSeam widthHi), deriv upperBeta z ≤ 0 := by
    intro z hz
    have hm := interior_subset hz
    rw [(upperBeta_hasDerivAt z).deriv]
    exact (upperBeta_slope_bounds hm.1 hm.2).2.le
  have hl : ∀ z ∈ interior (Set.Icc sourceSeam widthHi), -(1/4 : ℝ) ≤ deriv upperBeta z := by
    intro z hz
    have hm := interior_subset hz
    rw [(upperBeta_hasDerivAt z).deriv]
    exact (upperBeta_slope_bounds hm.1 hm.2).1.le
  have h₁ := (convex_Icc sourceSeam widthHi).image_sub_le_mul_sub_of_deriv_le hc hd hu
    a ⟨ha,hab.trans hb⟩ b ⟨ha.trans hab,hb⟩ hab
  have h₂ := (convex_Icc sourceSeam widthHi).mul_sub_le_image_sub_of_le_deriv hc hd hl
    a ⟨ha,hab.trans hb⟩ b ⟨ha.trans hab,hb⟩ hab
  constructor <;> linarith

theorem lowerBeta_comparison {a b : ℝ}
    (ha : widthLo ≤ a) (hab : a ≤ b) (hb : b ≤ sourceSeam) :
    lowerBeta b ≤ lowerBeta a ∧ lowerBeta a-(b-a)/4 ≤ lowerBeta b := by
  have hc : ContinuousOn lowerBeta (Set.Icc widthLo sourceSeam) := by
    unfold lowerBeta lowerGain upperGain; fun_prop
  have hd : DifferentiableOn ℝ lowerBeta (interior (Set.Icc widthLo sourceSeam)) :=
    fun z _ => (lowerBeta_hasDerivAt z).differentiableAt.differentiableWithinAt
  have hu : ∀ z ∈ interior (Set.Icc widthLo sourceSeam), deriv lowerBeta z ≤ 0 := by
    intro z hz
    have hm := interior_subset hz
    rw [(lowerBeta_hasDerivAt z).deriv]
    exact (lowerBeta_slope_bounds hm.1 hm.2).2.le
  have hl : ∀ z ∈ interior (Set.Icc widthLo sourceSeam), -(1/4 : ℝ) ≤ deriv lowerBeta z := by
    intro z hz
    have hm := interior_subset hz
    rw [(lowerBeta_hasDerivAt z).deriv]
    exact (lowerBeta_slope_bounds hm.1 hm.2).1.le
  have h₁ := (convex_Icc widthLo sourceSeam).image_sub_le_mul_sub_of_deriv_le hc hd hu
    a ⟨ha,hab.trans hb⟩ b ⟨ha.trans hab,hb⟩ hab
  have h₂ := (convex_Icc widthLo sourceSeam).mul_sub_le_image_sub_of_le_deriv hc hd hl
    a ⟨ha,hab.trans hb⟩ b ⟨ha.trans hab,hb⟩ hab
  constructor <;> linarith

/-- Finite-difference bounds across both polynomial branches and their actual seam. -/
theorem beta_comparison {a b : ℝ} (ha : widthLo ≤ a) (hab : a ≤ b) (hb : b ≤ widthHi) :
    beta b ≤ beta a ∧ beta a-(b-a)/4 ≤ beta b := by
  by_cases haS : sourceSeam ≤ a
  · rw [beta_upper haS,beta_upper (haS.trans hab)]
    exact upperBeta_comparison haS hab hb
  · by_cases hbS : b ≤ sourceSeam
    · rw [beta_lower (le_of_not_ge haS),beta_lower hbS]
      exact lowerBeta_comparison ha hab hbS
    · have hl := lowerBeta_comparison ha (le_of_not_ge haS) le_rfl
      have hu := upperBeta_comparison le_rfl (le_of_not_ge hbS) hb
      rw [beta_seam_join] at hl
      rw [beta_lower (le_of_not_ge haS),beta_upper (le_of_not_ge hbS)]
      constructor <;> linarith

/-- The authentic Q.2 source satisfies all source hypotheses of the crossover
reduction on the actual tested interval. Only the explicit face parameters and
their sign/range guards remain. -/
theorem actual_witnessPrice_minimal {f fee kLower kUpper F H M z : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1/2) (hkLower : 2/5 ≤ kLower)
    (hkOrder : kLower ≤ kUpper) (hF : F ≤ 0) (hH : 0 ≤ H)
    (hstar₀ : widthLo ≤ witnessCrossover kUpper F H M)
    (hstar₁ : witnessCrossover kUpper F H M ≤ widthHi)
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    witnessPrice beta f fee kLower kUpper F H M (witnessCrossover kUpper F H M) ≤
      witnessPrice beta f fee kLower kUpper F H M z := by
  apply witnessPrice_minimal_of_comparisons (L := 1/4) hf₀ (by linarith)
    hkOrder hF hH (by nlinarith)
  · intro hleft
    exact (beta_comparison hz₀ hleft hstar₁).1
  · intro hright
    have h := (beta_comparison hstar₀ hright hz₁).2
    linarith

theorem beta_positive {z : ℝ} (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    (1/4000 : ℝ) < beta z := by
  have hb : (1/4000 : ℝ) < beta widthHi := by
    norm_num [beta,betaSlope,betaIntercept,g1Receipt,g0Receipt,sourceGain,
      upperGain,sourceY,sourceSeam,widthHi]
  exact hb.trans_le (beta_comparison hz₀ hz₁ le_rfl).1

/-- Q.2's literal crossover width as a function of the continuous cutoff offset. -/
def offsetWidth (m ε step v density k ξ : ℝ) : ℝ :=
  m+ε-ξ-3*ε-(v/(density*k))*max 0 (ξ-step-3*ε)

/-- The price used by the authentic continuous stationary-point checker,
including the allocated constant debit. -/
def offsetPrice (f fee m ε step v density k ξ : ℝ) : ℝ :=
  f*beta (offsetWidth m ε step v density k ξ)-k*(ξ+3*ε)/2-fee

/-- The positive-part speed switch costs at most the original offset displacement. -/
theorem positivePart_increment {a b c : ℝ} (hab : a ≤ b) :
    0 ≤ max 0 (b-c)-max 0 (a-c) ∧
      max 0 (b-c)-max 0 (a-c) ≤ b-a := by
  constructor
  · exact sub_nonneg.mpr (max_le_max le_rfl (sub_le_sub_right hab c))
  · have h : max 0 (b-c) ≤ max 0 (a-c)+(b-a) := by
      apply max_le
      · linarith [le_max_left (0 : ℝ) (a-c)]
      · linarith [le_max_right (0 : ℝ) (a-c)]
    linarith

/-- Every actual crossover moves left as the offset increases, through its
speed switch. This also certifies the full interval from its endpoint widths. -/
theorem offsetWidth_antitone {m ε step v density k a b : ℝ}
    (hv : 0 ≤ v) (hd : 0 < density) (hk : 0 < k) (hab : a ≤ b) :
    offsetWidth m ε step v density k b ≤ offsetWidth m ε step v density k a := by
  have hp := (positivePart_increment (c := step+3*ε) hab).1
  have hc : 0 ≤ v/(density*k) := div_nonneg hv (mul_pos hd hk).le
  have hm := mul_nonneg hc hp
  unfold offsetWidth
  have ha : a-step-3*ε = a-(step+3*ε) := by ring
  have hb : b-step-3*ε = b-(step+3*ε) := by ring
  rw [ha,hb]
  nlinarith

/-- Exact guard from the manuscript for the maximum crossover speed. -/
theorem offset_ratio_le_six {v density k : ℝ}
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 5/6) (hd : 39/100 ≤ density) (hk : 2/5 ≤ k) :
    0 ≤ v/(density*k) ∧ v/(density*k) ≤ 6 := by
  have hd₀ : 0 < density := by linarith
  have hk₀ : 0 < k := by linarith
  have hprod : (39/100 : ℝ)*(2/5) ≤ density*k :=
    mul_le_mul hd hk (by norm_num) hd₀.le
  constructor
  · exact div_nonneg hv₀ (mul_pos hd₀ hk₀).le
  · apply (div_le_iff₀ (mul_pos hd₀ hk₀)).2
    nlinarith

/-- The literal Q.2 crossover has the stated maximum speed seven, globally
through the positive-part switch, without a differentiability assumption. -/
theorem offsetWidth_speed {m ε step v density k a b : ℝ}
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 5/6) (hd : 39/100 ≤ density) (hk : 2/5 ≤ k)
    (hab : a ≤ b) :
    offsetWidth m ε step v density k a-7*(b-a) ≤ offsetWidth m ε step v density k b := by
  have hp := positivePart_increment (c := step+3*ε) hab
  have hc := offset_ratio_le_six hv₀ hv₁ hd hk
  have hm := mul_le_mul hc.2 hp.2 hp.1 (by norm_num : (0 : ℝ) ≤ 6)
  unfold offsetWidth
  have ha : a-step-3*ε = a-(step+3*ε) := by ring
  have hb : b-step-3*ε = b-(step+3*ε) := by ring
  rw [ha,hb]
  nlinarith

/-- The authentic continuous price decreases by at most half the cutoff
displacement. This uses its actual source monotonicity on both sides of the seam. -/
theorem offsetPrice_lower_difference {f fee m ε step v density k a b : ℝ}
    (hf : 0 ≤ f) (hv : 0 ≤ v) (hd : 0 < density) (hk₀ : 0 < k) (hk₁ : k ≤ 1)
    (hab : a ≤ b)
    (hb : widthLo ≤ offsetWidth m ε step v density k b)
    (ha : offsetWidth m ε step v density k a ≤ widthHi) :
    offsetPrice f fee m ε step v density k a-(b-a)/2 ≤
      offsetPrice f fee m ε step v density k b := by
  have hw := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk₀ hab
  have hβ := (beta_comparison hb hw ha).1
  have hm := mul_le_mul_of_nonneg_left hβ hf
  have hk := mul_le_mul_of_nonneg_right hk₁ (sub_nonneg.mpr hab)
  unfold offsetPrice
  nlinarith

/-- Soundness of the frozen checker's stationary-enclosure debit. For every
offset in a rational bisection bracket, the actual price is above the lesser
endpoint price minus ten times the bracket width. All intermediate crossover
widths are covered from the two endpoint guards. -/
theorem stationary_enclosure_lower {f fee m ε step v density k a b ξ : ℝ}
    (hf : 0 ≤ f) (hv : 0 ≤ v) (hd : 0 < density) (hk₀ : 0 < k) (hk₁ : k ≤ 1)
    (haξ : a ≤ ξ) (hξb : ξ ≤ b)
    (hb : widthLo ≤ offsetWidth m ε step v density k b)
    (ha : offsetWidth m ε step v density k a ≤ widthHi) :
    min (offsetPrice f fee m ε step v density k a)
        (offsetPrice f fee m ε step v density k b)-10*(b-a) ≤
      offsetPrice f fee m ε step v density k ξ := by
  have hbξ := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk₀ hξb
  have hp := offsetPrice_lower_difference (fee := fee) hf hv hd hk₀ hk₁ haξ (hb.trans hbξ) ha
  have hmin := min_le_left (offsetPrice f fee m ε step v density k a)
    (offsetPrice f fee m ε step v density k b)
  linarith

/-- Literal identification of the frozen bank's crossover with the continuous
offset formula used for the price test. -/
theorem bank_crossover_eq {m ε step v density k ξ : ℝ} (hk : k ≠ 0) (hd : density ≠ 0) :
    witnessCrossover k (-k*(ξ+3*ε)) ((v/density)*max 0 (ξ-step-3*ε)) (m+ε) =
      offsetWidth m ε step v density k ξ := by
  exact witnessCrossover_bank_eq hk hd

/-- The authentic price at every intermediate ordinary length is paid by the
actual continuous offset price. This specializes both source and deficit faces
to Q.2; it assumes no source monotonicity, derivative, or price conclusion. -/
theorem bank_witnessPrice_lower {f fee m ε step v density kLower kUpper ξ z : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1/2) (hv : 0 ≤ v) (hd : 0 < density)
    (hkLower : 2/5 ≤ kLower) (hkOrder : kLower ≤ kUpper)
    (hε : 0 ≤ ε) (hξ : 0 ≤ ξ)
    (hstar₀ : widthLo ≤ offsetWidth m ε step v density kUpper ξ)
    (hstar₁ : offsetWidth m ε step v density kUpper ξ ≤ widthHi)
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    offsetPrice f fee m ε step v density kUpper ξ ≤
      witnessPrice beta f fee kLower kUpper (-kUpper*(ξ+3*ε))
        ((v/density)*max 0 (ξ-step-3*ε)) (m+ε) z := by
  have hk : 0 < kUpper := by linarith
  have hF : -kUpper*(ξ+3*ε) ≤ 0 := by nlinarith
  have hH : 0 ≤ (v/density)*max 0 (ξ-step-3*ε) := by positivity
  have hcross := bank_crossover_eq (m := m) (ε := ε) (step := step) (v := v)
    (ξ := ξ) (ne_of_gt hk) (ne_of_gt hd)
  have hm := actual_witnessPrice_minimal (fee := fee) hf₀ hf₁ hkLower hkOrder hF hH
    (hcross.symm ▸ hstar₀) (hcross.symm ▸ hstar₁) hz₀ hz₁
  rw [witnessPrice_at_crossover hk hF hH, hcross] at hm
  unfold offsetPrice
  nlinarith

/-- Sound scalar consumer for a stationary-node certificate: its conservative
enclosure value bounds every offset in the bracket and every tested ordinary
length with the authentic three deficit faces. The endpoint guards imply all
intermediate crossover guards, including the source seam and speed switch. -/
theorem stationary_enclosure_pays_all_lengths
    {f fee m ε step v density kLower kUpper a b ξ z : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1/2) (hv : 0 ≤ v) (hd : 0 < density)
    (hkLower : 2/5 ≤ kLower) (hkOrder : kLower ≤ kUpper) (hkUpper : kUpper ≤ 1)
    (hε : 0 ≤ ε) (ha₀ : 0 ≤ a) (haξ : a ≤ ξ) (hξb : ξ ≤ b)
    (hb : widthLo ≤ offsetWidth m ε step v density kUpper b)
    (ha : offsetWidth m ε step v density kUpper a ≤ widthHi)
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    min (offsetPrice f fee m ε step v density kUpper a)
        (offsetPrice f fee m ε step v density kUpper b)-10*(b-a) ≤
      witnessPrice beta f fee kLower kUpper (-kUpper*(ξ+3*ε))
        ((v/density)*max 0 (ξ-step-3*ε)) (m+ε) z := by
  have hk : 0 < kUpper := by linarith
  have h₁ := stationary_enclosure_lower (fee := fee) hf₀ hv hd hk hkUpper haξ hξb hb ha
  have hbξ := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk hξb
  have hξa := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk haξ
  exact h₁.trans (bank_witnessPrice_lower hf₀ hf₁ hv hd hkLower hkOrder hε
    (ha₀.trans haξ) (hb.trans hbξ) (hξa.trans ha) hz₀ hz₁)

/-! A concrete, actually present nonstationary mixed terminal. Its new
conservative budget is proved from the literal physical polynomial, not taken
from the terminal's stored normalized or physical numerator. -/

/-- Original cell 35, trace event 35345, the first nonstationary mixed terminal. -/
def ticketBox : QRH.Coverage.Box :=
  ⟨407/1024,815/2048,1019/2048,2039/4096⟩

theorem ticketBox_actual : ∃ leaf ∈ QRH.PhysicalCertificate.forestRecords
    QRH.PhysicalCertificate.qForest, leaf.box = ticketBox ∧ leaf.route = .mixed := by
  have h : (QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest).any
      (fun leaf => decide (leaf.box = ticketBox ∧ leaf.route = .mixed)) = true := by
    decide +kernel
  simpa only [List.any_eq_true,decide_eq_true_eq] using h

/-- Both authentic conductor endpoints pass the tensor check for a small
negative cleared margin. This is a fresh check of 18 generated coefficients. -/
theorem ticket_cleared_checks :
    QRH.Bernstein.coefficientsCheck 2 2
      (QRH.Cycle092.Physical.priceCoefficients (8175840773/10000000000) ticketBox)
      (-(1/1000000)) = true ∧
    QRH.Bernstein.coefficientsCheck 2 2
      (QRH.Cycle092.Physical.priceCoefficients (8175840793/10000000000) ticketBox)
      (-(1/1000000)) = true := by
  decide +kernel

theorem ticket_cleared_lower {h : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : ticketBox.Contains point) :
    -(1/1000000 : ℝ) ≤ QRH.Cycle092.Physical.clearedProxy h point.1 point.2 := by
  have hu : ticketBox.uLo < ticketBox.uHi := by norm_num [ticketBox]
  have hv : ticketBox.vLo < ticketBox.vHi := by norm_num [ticketBox]
  have hl := QRH.Cycle092.Physical.generated_box_bound (8175840773/10000000000)
    ticketBox (-(1/1000000)) hu hv ticket_cleared_checks.1 hp
  have hr := QRH.Cycle092.Physical.generated_box_bound (8175840793/10000000000)
    ticketBox (-(1/1000000)) hu hv ticket_cleared_checks.2 hp
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg] at hl hr
  change -(1/1000000 : ℝ) ≤ QRH.Cycle092.Physical.clearedProxy hLower point.1 point.2 at hl
  change -(1/1000000 : ℝ) ≤ QRH.Cycle092.Physical.clearedProxy hUpper point.1 point.2 at hr
  have hs := QRH.Bernstein.coordinate_mem_unit conductor_interval.2.1 hh hh'
  change 0 ≤ (h-hLower)/(hUpper-hLower) ∧ (h-hLower)/(hUpper-hLower) ≤ 1 at hs
  rw [QRH.Cycle092.Physical.cleared_interpolation]
  have h₀ := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ 1-(h-hLower)/(hUpper-hLower))
  have h₁ := mul_le_mul_of_nonneg_left hr hs.1
  nlinarith

/-- An actual uniform upper bound for the original Q1 top price on this
entire mixed terminal, at every certified real contact and conductor. -/
theorem ticket_top_budget {h g₀ g₁ : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : ticketBox.Contains point)
    (hg₀ : 5805911/100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913/100000000)
    (hg₁ : 3799809/50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981/5000000) :
    QRH.Cycle092.Physical.price h point.1 point.2 g₀ g₁ h-theta ≤ 1/1000000 := by
  have hd : 0 ≤ point.1 := by have h := hp.1; norm_num [ticketBox] at h; linarith
  have hd' : point.1 ≤ 1/2 := by have h := hp.2.1; norm_num [ticketBox] at h; linarith
  have hpa : 0 ≤ point.2 := by have h := hp.2.2.1; norm_num [ticketBox] at h; linarith
  have hpa' : point.2 ≤ 1/2 := by have h := hp.2.2.2; norm_num [ticketBox] at h; linarith
  have hc := QRH.Cycle092.Physical.actual_capacity_lower hh hh'
  have hr := QRH.Cycle092.Physical.count_upper hd hd' hpa hpa' hg₀ hg₀' hg₁ hg₁'
  have hj := QRH.Cycle092.Physical.admitted hd hd' hpa hpa'
    (by norm_num : (0 : ℝ) ≤ 5805911/100000000)
    (by norm_num : (5805911/100000000 : ℝ) ≤ 3/50)
    (by norm_num : (7/100 : ℝ) ≤ 379981/5000000)
    (by norm_num : (379981/5000000 : ℝ) ≤ 2/25)
  have hdk : 0 ≤ point.1*pairedK point.2 (379981/5000000) := by
    apply mul_nonneg hd
    unfold pairedK
    nlinarith
  have hj₀ : 1 ≤ pairedJ point.1 point.2 (379981/5000000) := by
    unfold pairedJ pairedV
    nlinarith
  have hclear := ticket_cleared_lower hh hh' hp
  have hdiv := cleared_margin_nonpositive (by norm_num : -(1/1000000 : ℝ) ≤ 0)
    hclear (by norm_num : (0 : ℝ) < 1) hj₀
  have he := pairedCount_clear_margin (d := point.1) (p := point.2)
    (g₀ := (5805911/100000000 : ℝ)) (g₁ := (379981/5000000 : ℝ))
    (target := theta) (base := QRH.Cycle092.Physical.baseProxy h point.1 point.2)
    (h := h) (ne_of_gt hj.2.1)
  change QRH.Cycle092.Physical.clearedProxy h point.1 point.2 = _ at he
  have hproxy : -(1/1000000 : ℝ) ≤ theta-
      (QRH.Cycle092.Physical.baseProxy h point.1 point.2+
        3*h*pairedCount point.1 point.2 (5805911/100000000) (379981/5000000)/4) := by
    rw [he] at hdiv
    simpa only [div_one,mul_div_cancel_left₀ _ (ne_of_gt hj.2.1)] using hdiv
  have hcap := mul_le_mul_of_nonneg_left hc (mul_nonneg hd hpa)
  have hcount := mul_le_mul_of_nonneg_left hr
    (by have h₀ := conductor_interval.1.le.trans hh; positivity : 0 ≤ 3*h/4)
  dsimp [QRH.Cycle092.Physical.price,QRH.Cycle092.Physical.baseProxy] at hproxy ⊢
  nlinarith

/-- Conservative normalized debit derived from the proved physical top bound. -/
def ticketBudget : ℝ := (1/1000000+inwardDebit)/hLower
def ticketGamma : ℝ := 18728551/5000000000000
def ticketV : ℝ := 5/6-815/2048
def ticketKLower : ℝ := pairedK (2039/4096) (g1Receipt.hi : ℝ)
def ticketKUpper : ℝ := pairedK (1019/2048) (g1Receipt.lo : ℝ)
def ticketM : ℝ := pairedCrossing (815/2048) (1019/2048)
  (g0Receipt.lo : ℝ) (g1Receipt.hi : ℝ)/3
def ticketFee : ℝ := (2039/4096)*witnessCollar/2+ticketBudget/(407/1024)

/-- The proved original physical top budget pays every lower nonnegative
conductor, with the actual separately allocated inward debit retained. -/
theorem ticket_normalized_physical_debit {h g₀ g₁ D : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : ticketBox.Contains point)
    (hg₀ : 5805911/100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913/100000000)
    (hg₁ : 3799809/50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981/5000000)
    (hD₀ : 0 ≤ D) (hDh : D ≤ h) :
    positivePart (QRH.Cycle092.Physical.price h point.1 point.2 g₀ g₁ D-theta+inwardDebit) ≤
      D*ticketBudget := by
  have hd : 0 ≤ point.1 := by have h := hp.1; norm_num [ticketBox] at h; linarith
  have hd' : point.1 ≤ 1/2 := by have h := hp.2.1; norm_num [ticketBox] at h; linarith
  have hdb : point.1 ≤ 815/2048 := by simpa only [ticketBox,Rat.cast_div,Rat.cast_ofNat] using hp.2.1
  have hpa : 0 ≤ point.2 := by have h := hp.2.2.1; norm_num [ticketBox] at h; linarith
  have hpa' : point.2 ≤ 1/2 := by have h := hp.2.2.2; norm_num [ticketBox] at h; linarith
  have hj := QRH.Cycle092.Physical.admitted hd hd' hpa hpa'
    (by linarith : 0 ≤ g₀) (by linarith : g₀ ≤ 3/50)
    (by linarith : 7/100 ≤ g₁) (by linarith : g₁ ≤ 2/25)
  have hR := pairedCount_lower hd (by linarith) hj.1 hj.2.1
  have hq : normalizedDebit (1/1000000) inwardDebit hLower = ticketBudget := by
    norm_num [normalizedDebit,ticketBudget]
  have htop := ticket_top_budget hh hh' hp hg₀ hg₀' hg₁ hg₁'
  rw [QRH.Cycle092.Physical.price_eq_conductorPrice] at htop ⊢
  have hnorm := normalized_physical_debit_Q2 hd hpa hpa' hdb
    physicalCap_admissible.1.le allowances_pos.1.le hR allowances_pos.2.2.2.2.le
    conductor_interval.1 hh hD₀ hDh
    (by rw [hq]; norm_num [ticketBudget,inwardDebit,hLower,boxSlope,physicalCap]) htop
  simpa only [hq] using hnorm

theorem ticket_parameter_guards :
    2/5 ≤ ticketKLower ∧ ticketKLower ≤ ticketKUpper ∧ ticketKUpper ≤ 1 ∧
    0 ≤ ticketGamma ∧
    4*ticketBudget/(3*ticketV) ≤ ticketGamma := by
  norm_num [ticketKLower,ticketKUpper,ticketGamma,ticketBudget,ticketV,
    pairedK,g1Receipt,inwardDebit,hLower]

/-- The complete offset bank stays inside the true source-price corridor. -/
theorem ticket_offset_endpoints :
    widthLo ≤ offsetWidth ticketM witnessCollar (ticketGamma/65536) ticketV (815/2048)
      ticketKUpper ticketGamma ∧
    offsetWidth ticketM witnessCollar (ticketGamma/65536) ticketV (815/2048)
      ticketKUpper 0 ≤ widthHi := by
  norm_num [offsetWidth,ticketM,ticketGamma,ticketV,ticketKUpper,pairedCrossing,pairedJ,
    pairedV,pairedK,pairedU,g0Receipt,g1Receipt,witnessCollar,widthLo,widthHi]

/-- A fresh exact check of the authentic price at both bank endpoints. The
enclosure debit is charged on the entire bank, so no stored margin or stationary
candidate is used in this concrete proof. -/
theorem ticket_offset_margin :
    (3/10000 : ℝ) ≤
      min (offsetPrice (1019/2048) ticketFee ticketM witnessCollar (ticketGamma/65536)
          ticketV (815/2048) ticketKUpper 0)
        (offsetPrice (1019/2048) ticketFee ticketM witnessCollar (ticketGamma/65536)
          ticketV (815/2048) ticketKUpper ticketGamma)-10*ticketGamma := by
  norm_num [offsetPrice,offsetWidth,beta,betaSlope,betaIntercept,sourceGain,lowerGain,upperGain,
    ticketFee,ticketBudget,ticketM,ticketGamma,ticketV,ticketKUpper,pairedCrossing,pairedJ,
    pairedV,pairedK,pairedU,g0Receipt,g1Receipt,witnessCollar,inwardDebit,hLower,
    sourceSeam,sourceY]

/-- Every actual offset and every admissible intermediate ordinary length on
this authentic mixed leaf has a positive scalar price reserve. -/
theorem ticket_all_offsets_lengths {ξ z : ℝ}
    (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ ticketGamma) (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    (3/10000 : ℝ) ≤ witnessPrice beta (1019/2048) ticketFee ticketKLower ticketKUpper
      (-ticketKUpper*(ξ+3*witnessCollar))
      ((ticketV/(815/2048))*max 0 (ξ-ticketGamma/65536-3*witnessCollar))
      (ticketM+witnessCollar) z := by
  have h := stationary_enclosure_pays_all_lengths
    (fee := ticketFee) (m := ticketM) (ε := witnessCollar)
    (step := ticketGamma/65536) (v := ticketV) (density := 815/2048)
    (kLower := ticketKLower) (kUpper := ticketKUpper) (a := 0) (b := ticketGamma)
    (by norm_num : (0 : ℝ) ≤ 1019/2048) (by norm_num : (1019/2048 : ℝ) ≤ 1/2)
    (by norm_num [ticketV]) (by norm_num) ticket_parameter_guards.1
    ticket_parameter_guards.2.1 ticket_parameter_guards.2.2.1
    (by norm_num [witnessCollar]) (by norm_num) hξ₀ hξ₁
    ticket_offset_endpoints.1 ticket_offset_endpoints.2 hz₀ hz₁
  have hm := ticket_offset_margin
  simp only [sub_zero] at h
  exact hm.trans h

/-! Local derivative guards retain the tighter ticket-dependent slope needed
by the nonstationary branch of the original checker. -/

theorem upperGainSlope_mono {a b : ℝ} (hab : a ≤ b) (hb : b ≤ sourceY) :
    upperGainSlope a ≤ upperGainSlope b := by
  have ht : 0 ≤ sourceY-b := sub_nonneg.mpr hb
  unfold upperGainSlope
  gcongr

theorem lowerGainSlope_mono {a b : ℝ} (hab : a ≤ b) :
    lowerGainSlope a ≤ lowerGainSlope b := by
  unfold lowerGainSlope
  linarith

theorem upperBeta_local_secant {a b L : ℝ} (hab : a ≤ b) (hb : b ≤ sourceY)
    (hL : -L ≤ betaSlope+upperGainSlope a) :
    betaSlope*a-betaIntercept+upperGain a-L*(b-a) ≤
      betaSlope*b-betaIntercept+upperGain b := by
  have hc : ContinuousOn upperBeta (Set.Icc a b) := by unfold upperBeta upperGain; fun_prop
  have hd : DifferentiableOn ℝ upperBeta (interior (Set.Icc a b)) :=
    fun z _ => (upperBeta_hasDerivAt z).differentiableAt.differentiableWithinAt
  have hl : ∀ z ∈ interior (Set.Icc a b), -L ≤ deriv upperBeta z := by
    intro z hz
    have hm := interior_subset hz
    rw [(upperBeta_hasDerivAt z).deriv]
    linarith [upperGainSlope_mono hm.1 (hm.2.trans hb)]
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hd hl
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  unfold upperBeta at h
  linarith

theorem lowerBeta_local_secant {a b L : ℝ} (hab : a ≤ b)
    (hL : -L ≤ betaSlope+lowerGainSlope a) :
    betaSlope*a-betaIntercept+lowerGain a-L*(b-a) ≤
      betaSlope*b-betaIntercept+lowerGain b := by
  have hc : ContinuousOn lowerBeta (Set.Icc a b) := by unfold lowerBeta lowerGain upperGain; fun_prop
  have hd : DifferentiableOn ℝ lowerBeta (interior (Set.Icc a b)) :=
    fun z _ => (lowerBeta_hasDerivAt z).differentiableAt.differentiableWithinAt
  have hl : ∀ z ∈ interior (Set.Icc a b), -L ≤ deriv lowerBeta z := by
    intro z hz
    have hm := interior_subset hz
    rw [(lowerBeta_hasDerivAt z).deriv]
    linarith [lowerGainSlope_mono hm.1]
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hd hl
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  unfold lowerBeta at h
  linarith

/-- The local source Lipschitz guard is proved from the two actual branch
derivatives, including their genuine seam jump. -/
theorem beta_local_secant {lo hi a b L : ℝ}
    (hlo : lo ≤ a) (hab : a ≤ b) (hhi : b ≤ hi) (hY : hi ≤ sourceY)
    (hl : lo ≤ sourceSeam → -L ≤ betaSlope+lowerGainSlope lo)
    (hu : sourceSeam ≤ hi → -L ≤ betaSlope+upperGainSlope (max sourceSeam lo)) :
    beta a-L*(b-a) ≤ beta b := by
  by_cases ha : sourceSeam ≤ a
  · have hmax : max sourceSeam lo ≤ a := max_le ha hlo
    have hbound := hu (ha.trans (hab.trans hhi))
    have hm := upperGainSlope_mono hmax (hab.trans (hhi.trans hY))
    rw [beta_upper ha,beta_upper (ha.trans hab)]
    exact upperBeta_local_secant hab (hhi.trans hY) (by linarith)
  · have hal : a ≤ sourceSeam := le_of_not_ge ha
    have hbound := hl (hlo.trans hal)
    have hm := lowerGainSlope_mono hlo
    by_cases hb : b ≤ sourceSeam
    · rw [beta_lower hal,beta_lower hb]
      exact lowerBeta_local_secant hab (by linarith)
    · have h₁ := lowerBeta_local_secant hal (by linarith : -L ≤ betaSlope+lowerGainSlope a)
      have hmax : max sourceSeam lo = sourceSeam := max_eq_left (hlo.trans hal)
      have h₂ := hu ((le_of_not_ge hb).trans hhi)
      rw [hmax] at h₂
      have h₃ := upperBeta_local_secant (le_of_not_ge hb) (hhi.trans hY) h₂
      rw [beta_lower hal,beta_upper (le_of_not_ge hb)]
      have hjoin := beta_seam_join
      unfold lowerBeta upperBeta at hjoin ⊢
      linarith

theorem offsetWidth_speed_exact {m ε step v density k a b : ℝ}
    (hv : 0 ≤ v) (hd : 0 < density) (hk : 0 < k) (hab : a ≤ b) :
    offsetWidth m ε step v density k a-(1+v/(density*k))*(b-a) ≤
      offsetWidth m ε step v density k b := by
  have hp := (positivePart_increment (c := step+3*ε) hab).2
  have hm := mul_le_mul_of_nonneg_left hp (div_nonneg hv (mul_pos hd hk).le)
  unfold offsetWidth
  have ha : a-step-3*ε = a-(step+3*ε) := by ring
  have hb : b-step-3*ε = b-(step+3*ε) := by ring
  rw [ha,hb]
  nlinarith

/-- The actual ticket derivative guard makes the full price decrease through
both source branches and both crossover-speed branches. -/
theorem offsetPrice_antitone_local
    {f fee m ε step v density k lo hi L a b : ℝ}
    (hf : 0 ≤ f) (hv : 0 ≤ v) (hd : 0 < density) (hk : 0 < k)
    (hL : 0 ≤ L) (hab : a ≤ b)
    (hlo : lo ≤ offsetWidth m ε step v density k b)
    (hhi : offsetWidth m ε step v density k a ≤ hi) (hY : hi ≤ sourceY)
    (hl : lo ≤ sourceSeam → -L ≤ betaSlope+lowerGainSlope lo)
    (hu : sourceSeam ≤ hi → -L ≤ betaSlope+upperGainSlope (max sourceSeam lo))
    (hpaid : f*L*(1+v/(density*k)) ≤ k/2) :
    offsetPrice f fee m ε step v density k b ≤ offsetPrice f fee m ε step v density k a := by
  have hw := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk hab
  have hb := beta_local_secant hlo hw hhi hY hl hu
  have hs := offsetWidth_speed_exact (m := m) (ε := ε) (step := step) hv hd hk hab
  have hm := mul_le_mul_of_nonneg_left hs hL
  have hβ : beta (offsetWidth m ε step v density k b)-beta (offsetWidth m ε step v density k a) ≤
      L*(1+v/(density*k))*(b-a) := by nlinarith
  have hmβ := mul_le_mul_of_nonneg_left hβ hf
  have hp := mul_le_mul_of_nonneg_right hpaid (sub_nonneg.mpr hab)
  unfold offsetPrice
  nlinarith

/-! Rational executable counterparts for authentic per-box mixed prices. -/

def qUpperGain (z : ℚ) : ℚ :=
  (2309/500)*(243/625-z)^2+(101/2)*(243/625-z)^3+(31/100000)*(243/625-z)-1/10000000
def qLowerGain (z : ℚ) : ℚ :=
  qUpperGain (747/2000)+(87/500)*(747/2000-z)+(67/10)*(747/2000-z)^2
def qGain (z : ℚ) : ℚ := if 747/2000 ≤ z then qUpperGain z else qLowerGain z
def qUpperSlope (z : ℚ) : ℚ :=
  -((2309/250)*(243/625-z)+(303/2)*(243/625-z)^2+31/100000)
def qLowerSlope (z : ℚ) : ℚ := -(87/500)-(67/5)*(747/2000-z)
def qBeta (z : ℚ) : ℚ := g1Receipt.lo*z-g0Receipt.hi/2+qGain z
def qOffsetWidth (m ε step v density k ξ : ℚ) : ℚ :=
  m+ε-ξ-3*ε-(v/(density*k))*max 0 (ξ-step-3*ε)
def qOffsetPrice (f fee m ε step v density k ξ : ℚ) : ℚ :=
  f*qBeta (qOffsetWidth m ε step v density k ξ)-k*(ξ+3*ε)/2-fee

theorem qUpperGain_cast (z : ℚ) : (qUpperGain z : ℝ) = upperGain z := by
  norm_num [qUpperGain,upperGain,sourceY]

theorem qLowerGain_cast (z : ℚ) : (qLowerGain z : ℝ) = lowerGain z := by
  norm_num [qLowerGain,qUpperGain,lowerGain,upperGain,sourceY,sourceSeam]

theorem qUpperSlope_cast (z : ℚ) : (qUpperSlope z : ℝ) = upperGainSlope z := by
  norm_num [qUpperSlope,upperGainSlope,sourceY]

theorem qLowerSlope_cast (z : ℚ) : (qLowerSlope z : ℝ) = lowerGainSlope z := by
  norm_num [qLowerSlope,lowerGainSlope,sourceSeam]

theorem qGain_cast (z : ℚ) : (qGain z : ℝ) = sourceGain z := by
  by_cases h : (747/2000 : ℚ) ≤ z
  · have hR : sourceSeam ≤ (z : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr h
      simpa only [Rat.cast_div,Rat.cast_ofNat,sourceSeam] using h
    simp only [qGain,ite_eq_left h,sourceGain,ite_eq_left hR,qUpperGain_cast]
  · have hR : ¬sourceSeam ≤ (z : ℝ) := by
      intro hz
      apply h
      apply (Rat.cast_le (K := ℝ)).mp
      simpa only [Rat.cast_div,Rat.cast_ofNat,sourceSeam] using hz
    simp only [qGain,ite_eq_right h,sourceGain,ite_eq_right hR,qLowerGain_cast]

theorem qBeta_cast (z : ℚ) : (qBeta z : ℝ) = beta z := by
  simp only [qBeta,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,
    qGain_cast,beta,betaSlope,betaIntercept]

theorem qOffsetWidth_cast (m ε step v density k ξ : ℚ) :
    (qOffsetWidth m ε step v density k ξ : ℝ) =
      offsetWidth m ε step v density k ξ := by
  simp only [qOffsetWidth,offsetWidth,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_div,Rat.cast_ofNat,Rat.cast_max,Rat.cast_zero]

theorem qOffsetPrice_cast (f fee m ε step v density k ξ : ℚ) :
    (qOffsetPrice f fee m ε step v density k ξ : ℝ) =
      offsetPrice f fee m ε step v density k ξ := by
  simp only [qOffsetPrice,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_ofNat,qBeta_cast,qOffsetWidth_cast,offsetPrice]

def rowBudget (B : ℚ) : ℚ := (max 0 B+1/1000000000000)/(8175840773/10000000000)
def rowV (box : QRH.Coverage.Box) : ℚ := 5/6-box.uHi
def rowKLower (box : QRH.Coverage.Box) : ℚ := 1-box.vHi*(1+2*g1Receipt.hi)
def rowKUpper (box : QRH.Coverage.Box) : ℚ := 1-box.vLo*(1+2*g1Receipt.lo)
def ceil13 (q : ℚ) : ℚ := (⌈q*10000000000000⌉ : ℤ)/10000000000000
def rowGamma (box : QRH.Coverage.Box) (B : ℚ) : ℚ :=
  ceil13 (4*rowBudget B/(3*rowV box))
def rowM (box : QRH.Coverage.Box) : ℚ :=
  (1+box.uHi*(1-box.vLo*(1+6*g0Receipt.lo-4*g1Receipt.hi))/
    (5/2-box.uHi*(1+2*box.vLo*(1+2*g1Receipt.hi))))/3
def rowFee (box : QRH.Coverage.Box) (B : ℚ) : ℚ :=
  box.vHi*(1/10000000000000)/2+rowBudget B/box.uLo
def rowWidth (box : QRH.Coverage.Box) (B ξ : ℚ) : ℚ :=
  qOffsetWidth (rowM box) (1/10000000000000) (rowGamma box B/65536)
    (rowV box) box.uHi (rowKUpper box) ξ
def rowPrice (box : QRH.Coverage.Box) (B ξ : ℚ) : ℚ :=
  qOffsetPrice box.vLo (rowFee box B) (rowM box) (1/10000000000000)
    (rowGamma box B/65536) (rowV box) box.uHi (rowKUpper box) ξ
def rowLo (box : QRH.Coverage.Box) (B : ℚ) : ℚ := rowWidth box B (rowGamma box B)
def rowHi (box : QRH.Coverage.Box) (B : ℚ) : ℚ := rowWidth box B 0
def rowAdverse (box : QRH.Coverage.Box) (B : ℚ) : ℚ := max 0
  (max (if rowLo box B ≤ 747/2000 then -g1Receipt.lo-qLowerSlope (rowLo box B) else 0)
    (if 747/2000 ≤ rowHi box B then
      -g1Receipt.lo-qUpperSlope (max (747/2000) (rowLo box B)) else 0))

/-- Every item is an exact arithmetic test of the literal price's parameters,
source derivatives and endpoint value. No stored terminal margin is read. -/
def nonstationaryCheck (box : QRH.Coverage.Box) (B : ℚ) : Bool := decide (
  0 ≤ box.vLo ∧ box.vLo ≤ 1/2 ∧ 0 < box.uLo ∧ 0 < box.uHi ∧ 0 ≤ rowV box ∧
  2/5 ≤ rowKLower box ∧ rowKLower box ≤ rowKUpper box ∧ rowKUpper box ≤ 1 ∧
  0 ≤ rowGamma box B ∧ 0 ≤ rowAdverse box B ∧
  4643/12500 ≤ rowLo box B ∧ rowHi box B ≤ 947/2500 ∧
  (rowLo box B ≤ 747/2000 → -rowAdverse box B ≤ g1Receipt.lo+qLowerSlope (rowLo box B)) ∧
  (747/2000 ≤ rowHi box B →
    -rowAdverse box B ≤ g1Receipt.lo+qUpperSlope (max (747/2000) (rowLo box B))) ∧
  box.vLo*rowAdverse box B*(1+rowV box/(box.uHi*rowKUpper box)) ≤ rowKUpper box/2 ∧
  1/2000000000 ≤ rowPrice box B (rowGamma box B))

/-- The rational row parameter `m` is exactly the actual paired-count crossing. -/
theorem rowM_cast (box : QRH.Coverage.Box) : (rowM box : ℝ) =
    pairedCrossing (box.uHi : ℝ) (box.vLo : ℝ) (g0Receipt.lo : ℝ) (g1Receipt.hi : ℝ)/3 := by
  norm_num [rowM,pairedCrossing,pairedJ,pairedV,pairedK,pairedU]
  congr 2
  ring

theorem rowWidth_cast (box : QRH.Coverage.Box) (B ξ : ℚ) :
    (rowWidth box B ξ : ℝ) = offsetWidth (rowM box) (1/10000000000000)
      ((rowGamma box B : ℝ)/65536) (rowV box) box.uHi (rowKUpper box) ξ := by
  simp only [rowWidth,qOffsetWidth_cast,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]

theorem rowPrice_cast (box : QRH.Coverage.Box) (B ξ : ℚ) :
    (rowPrice box B ξ : ℝ) = offsetPrice box.vLo (rowFee box B) (rowM box)
      (1/10000000000000) ((rowGamma box B : ℝ)/65536) (rowV box) box.uHi (rowKUpper box) ξ := by
  simp only [rowPrice,qOffsetPrice_cast,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]

/-- One checked authentic nonstationary row pays every real offset and every
intermediate length, with its computed `B`-normalized debit and receipt coefficients. -/
theorem nonstationaryCheck_sound (box : QRH.Coverage.Box) (B : ℚ)
    (hc : nonstationaryCheck box B = true) {ξ z : ℝ}
    (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ (rowGamma box B : ℝ))
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    (1/2000000000 : ℝ) ≤ witnessPrice beta box.vLo (rowFee box B)
      (rowKLower box) (rowKUpper box)
      (-(rowKUpper box : ℝ)*(ξ+3*(1/10000000000000)))
      (((rowV box : ℝ)/box.uHi)*max 0 (ξ-(rowGamma box B : ℝ)/65536-3*(1/10000000000000)))
      ((rowM box : ℝ)+1/10000000000000) z := by
  simp only [nonstationaryCheck,decide_eq_true_eq] at hc
  rcases hc with ⟨hf₀,hf₁,_,hd,hv,hkl,hko,hku,_,hL,hlo,hhi,hll,hlu,hpaid,hvalue⟩
  have hf₀R : (0 : ℝ) ≤ box.vLo := Rat.cast_nonneg.mpr hf₀
  have hf₁R : (box.vLo : ℝ) ≤ 1/2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hf₁
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hdR : (0 : ℝ) < box.uHi := Rat.cast_pos.mpr hd
  have hvR : (0 : ℝ) ≤ rowV box := Rat.cast_nonneg.mpr hv
  have hklR : (2/5 : ℝ) ≤ rowKLower box := by
    have h := (Rat.cast_le (K := ℝ)).mpr hkl
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  have hkoR : (rowKLower box : ℝ) ≤ rowKUpper box := Rat.cast_le.mpr hko
  have hkR : (0 : ℝ) < rowKUpper box := by linarith
  have hLR : (0 : ℝ) ≤ rowAdverse box B := Rat.cast_nonneg.mpr hL
  have hloR : widthLo ≤ (rowLo box B : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hlo
    simpa only [widthLo,Rat.cast_div,Rat.cast_ofNat] using h
  have hhiR : (rowHi box B : ℝ) ≤ widthHi := by
    have h := (Rat.cast_le (K := ℝ)).mpr hhi
    simpa only [widthHi,Rat.cast_div,Rat.cast_ofNat] using h
  have hloEq : (rowLo box B : ℝ) = offsetWidth (rowM box) (1/10000000000000)
      ((rowGamma box B : ℝ)/65536) (rowV box) box.uHi (rowKUpper box) (rowGamma box B) :=
    rowWidth_cast box B (rowGamma box B)
  have hhiEq : (rowHi box B : ℝ) = offsetWidth (rowM box) (1/10000000000000)
      ((rowGamma box B : ℝ)/65536) (rowV box) box.uHi (rowKUpper box) 0 := by
    simpa only [rowHi,Rat.cast_zero] using rowWidth_cast box B 0
  have hllR : (rowLo box B : ℝ) ≤ sourceSeam →
      -(rowAdverse box B : ℝ) ≤ betaSlope+lowerGainSlope (rowLo box B) := by
    intro h
    have hq : rowLo box B ≤ 747/2000 := by
      apply (Rat.cast_le (K := ℝ)).mp
      simpa only [sourceSeam,Rat.cast_div,Rat.cast_ofNat] using h
    have he := (Rat.cast_le (K := ℝ)).mpr (hll hq)
    simpa only [Rat.cast_neg,Rat.cast_add,qLowerSlope_cast,betaSlope] using he
  have hluR : sourceSeam ≤ (rowHi box B : ℝ) →
      -(rowAdverse box B : ℝ) ≤ betaSlope+upperGainSlope (max sourceSeam (rowLo box B : ℝ)) := by
    intro h
    have hq : (747/2000 : ℚ) ≤ rowHi box B := by
      apply (Rat.cast_le (K := ℝ)).mp
      simpa only [sourceSeam,Rat.cast_div,Rat.cast_ofNat] using h
    have he := (Rat.cast_le (K := ℝ)).mpr (hlu hq)
    simpa only [Rat.cast_neg,Rat.cast_add,qUpperSlope_cast,Rat.cast_max,
      Rat.cast_div,Rat.cast_ofNat,sourceSeam,betaSlope] using he
  have hpaidR : (box.vLo : ℝ)*(rowAdverse box B : ℝ)*
      (1+(rowV box : ℝ)/((box.uHi : ℝ)*(rowKUpper box : ℝ))) ≤ (rowKUpper box : ℝ)/2 := by
    exact_mod_cast hpaid
  have hvalR : (1/2000000000 : ℝ) ≤ offsetPrice box.vLo (rowFee box B) (rowM box)
      (1/10000000000000) ((rowGamma box B : ℝ)/65536) (rowV box) box.uHi (rowKUpper box)
      (rowGamma box B) := by
    have he := (Rat.cast_le (K := ℝ)).mpr hvalue
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,rowPrice_cast] using he
  have hξw := offsetWidth_antitone (m := (rowM box : ℝ)) (ε := 1/10000000000000)
    (step := (rowGamma box B : ℝ)/65536) hvR hdR hkR hξ₀
  have hγw := offsetWidth_antitone (m := (rowM box : ℝ)) (ε := 1/10000000000000)
    (step := (rowGamma box B : ℝ)/65536) hvR hdR hkR hξ₁
  have hmin := offsetPrice_antitone_local (fee := (rowFee box B : ℝ)) hf₀R hvR hdR hkR hLR hξ₁
    (by rw [← hloEq]) (hξw.trans (le_of_eq hhiEq.symm))
    (hhiR.trans width_corridor.2.2.2.le) hllR hluR hpaidR
  exact (hvalR.trans hmin).trans (bank_witnessPrice_lower hf₀R hf₁R hvR hdR hklR hkoR
    (by norm_num) hξ₀ (by rw [← hloEq] at hγw; exact hloR.trans hγw)
    (hξw.trans (by rw [← hhiEq]; exact hhiR)) hz₀ hz₁)


/-- The exact events requiring the separate segment/stationary route. -/
def stationaryEvents : List ℕ := [35216,35223,35228,35233,35240,35245,35250,35255,35260,
  35265,35270,35275,35280,35285,35290,35295,35312,35318,35323,35328,35333,35338,
  35361,35367,35373,35379,35384,35411,35417,35423,35429,35461,35467,35473,35511,35517,35559]

def rowChecked (r : QRH.Cycle092.TopData.Row) : Bool :=
  if r.event ∈ stationaryEvents then true else nonstationaryCheck r.box r.B

set_option maxHeartbeats 0 in
 theorem actual_group00_checked : QRH.Cycle092.TopData.group00.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group01_checked : QRH.Cycle092.TopData.group01.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group02_checked : QRH.Cycle092.TopData.group02.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group03_checked : QRH.Cycle092.TopData.group03.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group04_checked : QRH.Cycle092.TopData.group04.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group05_checked : QRH.Cycle092.TopData.group05.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group06_checked : QRH.Cycle092.TopData.group06.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group07_checked : QRH.Cycle092.TopData.group07.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group08_checked : QRH.Cycle092.TopData.group08.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group09_checked : QRH.Cycle092.TopData.group09.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group10_checked : QRH.Cycle092.TopData.group10.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group11_checked : QRH.Cycle092.TopData.group11.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group12_checked : QRH.Cycle092.TopData.group12.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group13_checked : QRH.Cycle092.TopData.group13.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group14_checked : QRH.Cycle092.TopData.group14.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group15_checked : QRH.Cycle092.TopData.group15.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group16_checked : QRH.Cycle092.TopData.group16.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group17_checked : QRH.Cycle092.TopData.group17.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group18_checked : QRH.Cycle092.TopData.group18.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group19_checked : QRH.Cycle092.TopData.group19.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group20_checked : QRH.Cycle092.TopData.group20.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group21_checked : QRH.Cycle092.TopData.group21.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group22_checked : QRH.Cycle092.TopData.group22.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group23_checked : QRH.Cycle092.TopData.group23.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group24_checked : QRH.Cycle092.TopData.group24.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group25_checked : QRH.Cycle092.TopData.group25.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group26_checked : QRH.Cycle092.TopData.group26.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group27_checked : QRH.Cycle092.TopData.group27.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group28_checked : QRH.Cycle092.TopData.group28.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group29_checked : QRH.Cycle092.TopData.group29.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group30_checked : QRH.Cycle092.TopData.group30.all rowChecked = true := by
  decide +kernel

set_option maxHeartbeats 0 in
 theorem actual_group31_checked : QRH.Cycle092.TopData.group31.all rowChecked = true := by
  decide +kernel


/-- All nonstationary rows in the actual frozen mixed forest pass the literal
source/price checker; the explicitly named 37 stationary events stay separate. -/
theorem actual_rows_checked : QRH.Cycle092.TopData.rows.all rowChecked = true := by
  simp only [QRH.Cycle092.TopData.rows,List.all_append,
    actual_group00_checked,
    actual_group01_checked,
    actual_group02_checked,
    actual_group03_checked,
    actual_group04_checked,
    actual_group05_checked,
    actual_group06_checked,
    actual_group07_checked,
    actual_group08_checked,
    actual_group09_checked,
    actual_group10_checked,
    actual_group11_checked,
    actual_group12_checked,
    actual_group13_checked,
    actual_group14_checked,
    actual_group15_checked,
    actual_group16_checked,
    actual_group17_checked,
    actual_group18_checked,
    actual_group19_checked,
    actual_group20_checked,
    actual_group21_checked,
    actual_group22_checked,
    actual_group23_checked,
    actual_group24_checked,
    actual_group25_checked,
    actual_group26_checked,
    actual_group27_checked,
    actual_group28_checked,
    actual_group29_checked,
    actual_group30_checked,
    actual_group31_checked,Bool.and_self]

set_option maxHeartbeats 0 in
 theorem actual_nonstationary_count :
    (QRH.Cycle092.TopData.rows.filter fun r => r.event ∉ stationaryEvents).length = 9644 := by
  decide +kernel

/-- Every actual nonstationary mixed row, with its own authentic frozen top
bound, pays all real cutoff offsets and all tested ordinary lengths. -/
theorem actual_nonstationary_pays (r : QRH.Cycle092.TopData.Row)
    (hr : r ∈ QRH.Cycle092.TopData.rows) (hs : r.event ∉ stationaryEvents) {ξ z : ℝ}
    (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ (rowGamma r.box r.B : ℝ))
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    (1/2000000000 : ℝ) ≤ witnessPrice beta r.box.vLo (rowFee r.box r.B)
      (rowKLower r.box) (rowKUpper r.box)
      (-(rowKUpper r.box : ℝ)*(ξ+3*(1/10000000000000)))
      (((rowV r.box : ℝ)/r.box.uHi)*max 0
        (ξ-(rowGamma r.box r.B : ℝ)/65536-3*(1/10000000000000)))
      ((rowM r.box : ℝ)+1/10000000000000) z := by
  have hc := List.all_eq_true.mp actual_rows_checked r hr
  simp only [rowChecked,ite_eq_right hs] at hc
  exact nonstationaryCheck_sound r.box r.B hc hξ₀ hξ₁ hz₀ hz₁

end
end QRH.Cycle092.Mixed
