import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.PerturbedCentral

open SevenEighths.ProbeHighRowFamily
open SevenEighths.ProbeCentralExponent
open SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDetectorRawFiber

/-! Fixed perturbed geometry. -/

def rho0 : ℝ := 1 / 1000000

def totalE : ℝ := 1 / 6 + rho0

def sourceLx : ℝ := 17 / 48 - rho0 / 2

def sourceLy : ℝ := 23 / 48 - rho0 / 2

def physicalHeight : ℝ := 13 / 16 + 3 * rho0 / 2

def boundary : ℝ := 7 / 8 - rho0 / 4

def physicalDmin : ℝ := 1 / 200

def physicalDmax : ℝ := 7 / 8

def deltaGap (β : ℝ) : ℝ := β - boundary

def gammaCount (β : ℝ) : ℝ := max 0 (β - 7 / 8)

lemma rho0_pos : (0 : ℝ) < rho0 := by norm_num [rho0]
lemma rho0_nonneg : (0 : ℝ) ≤ rho0 := rho0_pos.le
lemma totalE_pos : (0 : ℝ) < totalE := by norm_num [totalE, rho0]
lemma totalE_ne : totalE ≠ 0 := totalE_pos.ne'
lemma totalE_ge_sixth : (1 / 6 : ℝ) ≤ totalE := by norm_num [totalE, rho0]
lemma totalE_le_one : totalE ≤ (1 : ℝ) := by norm_num [totalE, rho0]
lemma height_nonneg : (0 : ℝ) ≤ physicalHeight := by norm_num [physicalHeight, rho0]
lemma height_le_one : physicalHeight ≤ (1 : ℝ) := by norm_num [physicalHeight, rho0]
lemma height_ge_old : (13 / 16 : ℝ) ≤ physicalHeight := by norm_num [physicalHeight, rho0]
lemma sourceLy_nonneg : (0 : ℝ) ≤ sourceLy := by norm_num [sourceLy, rho0]
lemma physicalDmin_pos : (0 : ℝ) < physicalDmin := by norm_num [physicalDmin]
lemma physicalDmax_pos : (0 : ℝ) < physicalDmax := by norm_num [physicalDmax]
lemma physicalDmax_slot_top : physicalDmax ≤ (37 / 42 : ℝ) := by norm_num [physicalDmax]

lemma deltaGap_pos {β : ℝ} (hβ : boundary < β) : 0 < deltaGap β := by
  unfold deltaGap
  linarith

lemma deltaGap_nonneg {β : ℝ} (hβ : boundary ≤ β) : 0 ≤ deltaGap β := by
  unfold deltaGap
  linarith

lemma deltaGap_le_wide {β : ℝ} (hβ : β ≤ 1) : deltaGap β ≤ 9 / 40 := by
  unfold deltaGap boundary rho0
  norm_num at *
  linarith

lemma deltaGap_le_eighth_plus {β : ℝ} (hβ : β ≤ 1) :
    deltaGap β ≤ 1 / 8 + rho0 / 4 := by
  unfold deltaGap boundary
  linarith

lemma beta_shift_gap (β : ℝ) : β - 7 / 8 = deltaGap β - rho0 / 4 := by
  unfold deltaGap boundary
  ring

/-! The proposed `Gamma = max 0 (β-7/8)` has the desired scalar inequalities. -/

lemma gamma_nonneg (β : ℝ) : 0 ≤ gammaCount β := by
  exact le_max_left _ _

lemma gamma_le_eighth {β : ℝ} (hβ : β ≤ 1) : gammaCount β ≤ 1 / 8 := by
  unfold gammaCount
  rw [max_le_iff]
  constructor <;> linarith

lemma beta_energy_le_gamma (β : ℝ) :
    2 * β - 1 ≤ 3 / 4 + 2 * gammaCount β := by
  unfold gammaCount
  by_cases h : β - 7 / 8 ≤ 0
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

lemma gamma_gap_cancellation {β : ℝ} (hβ : boundary ≤ β) :
    -(β - 7 / 8) + physicalHeight * gammaCount β / 4 ≤ rho0 / 4 := by
  have hH : physicalHeight ≤ 1 := height_le_one
  unfold gammaCount
  by_cases h : β - 7 / 8 ≤ 0
  · rw [max_eq_left h]
    have hg := deltaGap_nonneg hβ
    rw [beta_shift_gap] at *
    linarith
  · have hp : 0 ≤ β - 7 / 8 := le_of_not_ge h
    rw [max_eq_right hp]
    have hm := mul_le_mul_of_nonneg_right hH (show 0 ≤ (β - 7 / 8) / 4 by positivity)
    nlinarith [rho0_nonneg]

/-!
`Moments` is monotone only from smaller `Δ` to larger `Δ`.  This is the exact
record-level direction relevant to the failed Gamma-transfer proposal.
-/

theorem moments_mono_delta
    {M : Ideal HeckeFamily.O}
    {H : Subgroup (HeckeFamily.O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : HeckeDetectorRawFiber.Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ₁ Δ₂ c κ C height εm : ℝ} (hΔ : Δ₁ ≤ Δ₂)
    (h : HeckeDetectorRawFiber.Moments F Δ₁ c κ C height εm) :
    HeckeDetectorRawFiber.Moments F Δ₂ c κ C height εm := by
  refine {
    inverse_raw := h.inverse_raw
    inverse_marked := h.inverse_marked
    plain_unmarked := h.plain_unmarked
    plain_marked := ?_
  }
  intro selected hselected hcap j k hjk s hs t ht
  apply h.plain_marked selected hselected ?_ j k hjk s hs t ht
  have hsum : 0 ≤ ∑ x ∈ selected, F.widths x := by
    apply Finset.sum_nonneg
    intro x hx
    exact (F.widths_pos x (hselected hx)).le
  have hc : 3 / 4 + 2 * Δ₁ ≤ 3 / 4 + 2 * Δ₂ := by linarith
  have hh := mul_le_mul_of_nonneg_right hc hsum
  nlinarith

/-- A concrete capacity-premise counterexample to the reverse Gamma transfer. -/
def betaGammaCounter : ℝ := 7 / 8 - rho0 / 8

lemma betaGammaCounter_range : boundary < betaGammaCounter ∧ betaGammaCounter < 7 / 8 := by
  norm_num [boundary, betaGammaCounter, rho0]

lemma gamma_reverse_capacity_counterexample :
    let β := betaGammaCounter
    let m : ℝ := 0
    let z : ℝ := 2 / 9
    2 * m + 6 * (3 / 4 + 2 * gammaCount β) * z ≤ 1 ∧
      ¬ (2 * m + 6 * (3 / 4 + 2 * deltaGap β) * z ≤ 1) := by
  norm_num [betaGammaCounter, gammaCount, deltaGap, boundary, rho0]

/-! Perturbed central source exponent, kept affine in the actual row/conductor variable. -/

def ellTau (ρ : ℝ) : ℝ := 1 / 6 + ρ

def lxTau (ρ : ℝ) : ℝ := 17 / 48 - ρ / 2

def lyTau (ρ : ℝ) : ℝ := 23 / 48 - ρ / 2

def heightTau (ρ : ℝ) : ℝ := 13 / 16 + 3 * ρ / 2

def sourceExponentTau (ρ a d R q : ℝ) : ℝ :=
  a - 7 / 8 + heightTau ρ * (17 / 50 - 1 / 6) - a * lyTau ρ -
    ellTau ρ / 2 + q * ellTau ρ +
      d * (R + (2 * a - 1) / 2 - 17 / 50)

def mixedSourceExponentTau (ρ a v d R q : ℝ) : ℝ :=
  sourceExponentTau ρ a v R q + (d - v) * R

lemma fixed_geometry_aliases :
    ellTau rho0 = totalE ∧ lxTau rho0 = sourceLx ∧ lyTau rho0 = sourceLy ∧
      heightTau rho0 = physicalHeight := by
  simp [ellTau, lxTau, lyTau, heightTau, totalE, sourceLx, sourceLy, physicalHeight]

lemma zero_matches_official_source (a d R q : ℝ) :
    sourceExponentTau 0 a d R q = ProbeCentralExponent.sourceExponent a d R q - 3 / 16 := by
  unfold sourceExponentTau heightTau lyTau ellTau ProbeCentralExponent.sourceExponent
  ring

lemma source_comparison (ρ a d R q : ℝ) :
    sourceExponentTau ρ a d R q - sourceExponentTau 0 a d R q =
      ρ * (1 / 100 + (2 * a - 1) / 4 + q) := by
  unfold sourceExponentTau heightTau lyTau ellTau
  ring

lemma mixed_comparison (ρ a v d R q : ℝ) :
    mixedSourceExponentTau ρ a v d R q =
      ProbeHighRowFamily.mixedSourceExponent a v d R q - 3 / 16 +
        ρ * (1 / 100 + (2 * a - 1) / 4 + q) := by
  unfold mixedSourceExponentTau ProbeHighRowFamily.mixedSourceExponent
  have hc := source_comparison ρ a v R q
  have hz := zero_matches_official_source a v R q
  linarith

lemma source_affine_in_d (ρ a d h R q : ℝ) :
    sourceExponentTau ρ a d R q = sourceExponentTau ρ a h R q +
      (d - h) * (R + (2 * a - 1) / 2 - 17 / 50) := by
  unfold sourceExponentTau
  ring

/-! Endpoint algebra copied into the additive namespace, now used with the real `rho0`. -/

def adaptiveRowCount (δ x : ℝ) : ℝ := Endpoint.balancedRowCount δ (1 / 2 - x)

lemma zero_balanced_identity (δ x : ℝ) :
    sourceExponentTau 0 ((1 + δ) / 2) (13 / 16) (adaptiveRowCount δ x) (δ * x) =
      Endpoint.balancedExponent δ (1 / 2 - x) := by
  unfold sourceExponentTau heightTau lyTau ellTau adaptiveRowCount Endpoint.balancedExponent
  ring

lemma adaptive_row_bounds (δ x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 - δ ≤ adaptiveRowCount δ x ∧
      adaptiveRowCount δ x ≤ 17 / 12 - 3 * δ / 2 := by
  let y : ℝ := 1 / 2 - x
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 / 2 := by dsimp [y]; linarith
  have hJ := Endpoint.balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have hJpos : 0 < Endpoint.balanceDenominator δ y := by linarith [hJ.1]
  have hP := Endpoint.primeWeight_bounds hy0 hy1
  have hD := Endpoint.denominator_bounds hy0 hy1
  have ha : 0 ≤ 5 / 6 - δ := by linarith
  have hJge : δ * Endpoint.primeWeight y ≤ Endpoint.balanceDenominator δ y := by
    have hn := mul_nonneg ha (show 0 ≤ Endpoint.denominator y by linarith [hD.1])
    dsimp [Endpoint.balanceDenominator]
    linarith
  have ht0 : 0 ≤ δ * Endpoint.primeWeight y / (2 * Endpoint.balanceDenominator δ y) :=
    div_nonneg (mul_nonneg hδ0 (by linarith [hP.1])) (by positivity)
  have ht1 : δ * Endpoint.primeWeight y / (2 * Endpoint.balanceDenominator δ y) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Endpoint.balanceDenominator δ y)).2
    linarith
  have hmul0 := mul_nonneg ha ht0
  have hmul1 := mul_le_mul_of_nonneg_left ht1 ha
  change 1 - δ ≤ Endpoint.balancedRowCount δ y ∧
    Endpoint.balancedRowCount δ y ≤ 17 / 12 - 3 * δ / 2
  unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
  constructor <;> nlinarith only [hmul0, hmul1]

lemma original_balanced_margin (δ x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    sourceExponentTau 0 ((1 + δ) / 2) (13 / 16) (adaptiveRowCount δ x) (δ * x) ≤
      -49 / 440640 := by
  rw [zero_balanced_identity]
  have hc := Endpoint.balanced_endpoint_margin hδ0 hδ1
    (show 0 ≤ 1 / 2 - x by linarith) (show 1 / 2 - x ≤ 1 / 2 by linarith)
  linarith

lemma endpoint_perturbation (ρ δ x : ℝ) :
    sourceExponentTau ρ ((1 + δ) / 2) (heightTau ρ) (adaptiveRowCount δ x) (δ * x) =
      sourceExponentTau 0 ((1 + δ) / 2) (13 / 16) (adaptiveRowCount δ x) (δ * x) +
        ρ * (3 * adaptiveRowCount δ x / 2 + δ + δ * x - 1 / 2) := by
  unfold sourceExponentTau heightTau lyTau ellTau adaptiveRowCount
  ring

lemma adaptive_endpoint_margin (ρ δ x : ℝ)
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    sourceExponentTau ρ ((1 + δ) / 2) (heightTau ρ) (adaptiveRowCount δ x) (δ * x) ≤
      -49 / 440640 + 13 * ρ / 8 := by
  rw [endpoint_perturbation]
  have hm := original_balanced_margin δ x hδ0 hδ1 hx0 hx1
  have hb := adaptive_row_bounds δ x hδ0 hδ1 hx0 hx1
  have hq := mul_le_mul_of_nonneg_left hx1 hδ0
  have hc : 3 * adaptiveRowCount δ x / 2 + δ + δ * x - 1 / 2 ≤ 13 / 8 := by
    nlinarith only [hb.2, hq, hδ0]
  have hp := mul_le_mul_of_nonneg_left hc hρ
  linarith

/-! Count-range and gap-cancellation lemmas for the actual `DeltaGap`, not Gamma. -/

lemma balanced_count_range_gap (δ x β L : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hβ0 : boundary ≤ β) (hβ1 : β ≤ 1) (hL0 : 0 ≤ L) (hL1 : L ≤ 1 / 32) :
    let R := adaptiveRowCount δ x + deltaGap β / 4 + L
    1 - δ ≤ R ∧ R ≤ 3 / 2 := by
  dsimp only
  have hb := adaptive_row_bounds δ x hδ0 hδ1 hx0 hx1
  have hΔ0 := deltaGap_nonneg hβ0
  have hΔ1 := deltaGap_le_eighth_plus hβ1
  constructor
  · linarith
  · have hρ : rho0 / 16 ≤ 1 / 192 := by norm_num [rho0]
    nlinarith [hb.2]

lemma gap_cancellation {β : ℝ} (hβ : boundary ≤ β) :
    -(β - 7 / 8) + physicalHeight * deltaGap β / 4 ≤ rho0 / 4 := by
  have hΔ := deltaGap_nonneg hβ
  have hH := height_le_one
  have hm := mul_le_mul_of_nonneg_right hH (show 0 ≤ deltaGap β / 4 by positivity)
  rw [beta_shift_gap]
  linarith

lemma balanced_mixed_margin_gap (δ x β L ζ μ v d : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hβ0 : boundary ≤ β) (hβ1 : β ≤ 1) (hL0 : 0 ≤ L) (hL1 : L ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hv : v ≤ physicalHeight + ζ)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) :
    let R := adaptiveRowCount δ x + deltaGap β / 4 + L
    mixedSourceExponentTau rho0 ((1 + δ) / 2) v d R (δ * x) - (β - 7 / 8) ≤
      -49 / 440640 + 15 * rho0 / 8 + physicalHeight * L + 2 * ζ + (3 / 2) * μ := by
  dsimp only
  let R := adaptiveRowCount δ x + deltaGap β / 4 + L
  have hr := balanced_count_range_gap δ x β L hδ0 hδ1 hx0 hx1 hβ0 hβ1 hL0 hL1
  change 1 - δ ≤ R ∧ R ≤ 3 / 2 at hr
  have hm := adaptive_endpoint_margin rho0 δ x rho0_nonneg hδ0 hδ1 hx0 hx1
  change sourceExponentTau rho0 ((1 + δ) / 2) physicalHeight (adaptiveRowCount δ x) (δ * x) ≤ -49 / 440640 + 13 * rho0 / 8 at hm
  have hs0 : 0 ≤ R + δ / 2 - 17 / 50 := by
    linarith [hr.1]
  have hs1 : R + δ / 2 - 17 / 50 ≤ 2 := by
    linarith [hr.2]
  have hrow : sourceExponentTau rho0 ((1 + δ) / 2) v R (δ * x) ≤
      sourceExponentTau rho0 ((1 + δ) / 2) physicalHeight R (δ * x) + 2 * ζ := by
    rw [source_affine_in_d rho0 ((1 + δ) / 2) v physicalHeight R (δ * x)]
    have ha : (2 * ((1 + δ) / 2) - 1) / 2 = δ / 2 := by ring
    rw [ha]
    have hp := mul_le_mul_of_nonneg_right (show v - physicalHeight ≤ ζ by linarith) hs0
    have hp' := mul_le_mul_of_nonneg_left hs1 hζ
    nlinarith
  have hRinc : sourceExponentTau rho0 ((1 + δ) / 2) physicalHeight R (δ * x) =
      sourceExponentTau rho0 ((1 + δ) / 2) physicalHeight (adaptiveRowCount δ x) (δ * x) +
        physicalHeight * (deltaGap β / 4 + L) := by
    unfold sourceExponentTau R
    ring
  have hgap := gap_cancellation hβ0
  have hmix : (d - v) * R ≤ μ * (3 / 2) := by
    have h1 := mul_le_mul_of_nonneg_right hdv (show 0 ≤ R by linarith [hr.1, hδ1])
    have h2 := mul_le_mul_of_nonneg_left hr.2 hμ
    linarith
  change sourceExponentTau rho0 ((1 + δ) / 2) v R (δ * x) + (d - v) * R - (β - 7 / 8) ≤ _
  rw [hRinc] at hrow
  nlinarith

lemma high_mixed_margin_gap (δ q β L ζ μ v d : ℝ)
    (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ δ / 2)
    (hβ0 : boundary ≤ β) (hL0 : 0 ≤ L) (hL1 : L ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hv : v ≤ physicalHeight + ζ)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) :
    mixedSourceExponentTau rho0 ((1 + δ) / 2) v d (1 - δ + L) q - (β - 7 / 8) ≤
      -49 / 440640 + 15 * rho0 / 8 + physicalHeight * L + 2 * ζ + (3 / 2) * μ := by
  have hvOld : v ≤ 13 / 16 + (ζ + 3 * rho0 / 2) := by
    unfold physicalHeight at hv
    linarith
  have hζOld : 0 ≤ ζ + 3 * rho0 / 2 := by linarith [rho0_nonneg]
  have hm := ProbeHighRowFamily.high_mixed_margin δ q 0 L (ζ + 3 * rho0 / 2) μ v d
    hδ0 hδ1 hq1 hL0 hL1 hζOld hvOld hμ hdv
  have hc := mixed_comparison rho0 ((1 + δ) / 2) v d (1 - δ + L) q
  have hpert : rho0 * (1 / 100 + δ / 4 + q) ≤ rho0 * (19 / 25) := by
    have hq2 : q ≤ 1 / 2 := hq1.trans (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) rho0_nonneg
  have hshift : -(β - 7 / 8) ≤ rho0 / 4 := by
    have hg := deltaGap_nonneg hβ0
    rw [beta_shift_gap]
    linarith
  have hH : (13 / 16 : ℝ) ≤ physicalHeight := height_ge_old
  have hHL := mul_le_mul_of_nonneg_right hH hL0
  rw [hc]
  norm_num only at hm
  norm_num [rho0] at *
  nlinarith

/-! The remaining named scalar branches from the packet. -/

/-- Perturbed floor branch, compared directly to the actual beta. -/
lemma floor_source_margin_gap (q β ζ d : ℝ)
    (hq : q ≤ 1 / 100) (hβ : boundary ≤ β)
    (hζ : 0 ≤ ζ) (hd : d ≤ physicalHeight + ζ) :
    sourceExponentTau rho0 (51 / 100) d 1 q - (β - 7 / 8) ≤
      -49 / 440640 + 15 * rho0 / 8 + 2 * ζ := by
  have hζOld : 0 ≤ ζ + 3 * rho0 / 2 := by linarith [rho0_nonneg]
  have hdOld : d ≤ 13 / 16 + (ζ + 3 * rho0 / 2) := by
    unfold physicalHeight at hd
    linarith
  have hm := ProbeCentralExponent.floor_source_margin q 0 (ζ + 3 * rho0 / 2) d
    hq hζOld hdOld
  have hc := source_comparison rho0 (51 / 100) d 1 q
  have hc0 := zero_matches_official_source (51 / 100) d 1 q
  have hc' : sourceExponentTau rho0 (51 / 100) d 1 q =
      ProbeCentralExponent.sourceExponent (51 / 100) d 1 q - 3 / 16 +
        rho0 * (1 / 100 + (2 * (51 / 100 : ℝ) - 1) / 4 + q) := by
    linarith
  have hpert : rho0 * (1 / 100 + (2 * (51 / 100 : ℝ) - 1) / 4 + q) ≤
      rho0 / 40 := by
    apply mul_le_mul_of_nonneg_left _ rho0_nonneg
    linarith
  have hshift : -(β - 7 / 8) ≤ rho0 / 4 := by
    have hg := deltaGap_nonneg hβ
    rw [beta_shift_gap]
    linarith
  rw [hc']
  norm_num only at hm
  norm_num [rho0] at *
  nlinarith

/-- Perturbed intermediate branch (`d ≤ 1/2`), again against actual beta. -/
lemma intermediate_source_margin_gap (δ q β d : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hq : q ≤ δ / 2)
    (hβ : boundary ≤ β) (hd : d ≤ 1 / 2) :
    sourceExponentTau rho0 ((1 + δ) / 2) d (76 / 75 - (2 / 3) * δ) q -
        (β - 7 / 8) ≤
      -49 / 440640 + 15 * rho0 / 8 := by
  have hm := ProbeCentralExponent.intermediate_source_margin δ q 0 d hδ0 hδ1 hq hd
  have hc := source_comparison rho0 ((1 + δ) / 2) d (76 / 75 - (2 / 3) * δ) q
  have hc0 := zero_matches_official_source ((1 + δ) / 2) d (76 / 75 - (2 / 3) * δ) q
  have hc' : sourceExponentTau rho0 ((1 + δ) / 2) d (76 / 75 - (2 / 3) * δ) q =
      ProbeCentralExponent.sourceExponent ((1 + δ) / 2) d (76 / 75 - (2 / 3) * δ) q - 3 / 16 +
        rho0 * (1 / 100 + (2 * ((1 + δ) / 2) - 1) / 4 + q) := by
    linarith
  have hpert : rho0 * (1 / 100 + (2 * ((1 + δ) / 2) - 1) / 4 + q) ≤
      rho0 * (127 / 200) := by
    apply mul_le_mul_of_nonneg_left _ rho0_nonneg
    linarith
  have hshift : -(β - 7 / 8) ≤ rho0 / 4 := by
    have hg := deltaGap_nonneg hβ
    rw [beta_shift_gap]
    linarith
  rw [hc']
  norm_num only at hm
  norm_num [rho0] at *
  nlinarith


/-! Exact shifted physical scale and total-E arithmetic identity. -/

def scaleExponentTau (ρ a e : ℝ) : ℝ :=
  lxTau ρ * (4 / 25) + a + 16 * e - 33 / 50 + lyTau ρ * (-a - 6 * e)

def arithmeticExponentTotal (E : ℝ) (N : ℕ)
    (a v d R q e eps loss mesh : ℝ) : ℝ :=
  d * R + v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss +
    E * (-(4 / 25) + q + mesh)

def realLossTau (ρ : ℝ) (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16 - 6 * lyTau ρ + 12 * v) * e + v * eps * (N + 8) + loss + ellTau ρ * mesh

lemma shifted_physical_scale_identity (Z ρ a e : ℝ) (hZ : 0 < Z) :
    (Z ^ (lxTau ρ)) ^ (4 / 25 : ℝ) * Z ^ (a + 16 * e - 33 / 50) *
        (Z ^ (lyTau ρ)) ^ (-a - 6 * e) =
      Z ^ (scaleExponentTau ρ a e) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold scaleExponentTau
  ring

lemma central_class_exponent_identity_total (N : ℕ)
    (ρ a v d R q e eps loss mesh overhead : ℝ) :
    scaleExponentTau ρ a e + overhead +
      arithmeticExponentTotal (ellTau ρ) N a v d R q e eps loss mesh =
    3 / 16 + mixedSourceExponentTau ρ a v d R q +
      realLossTau ρ N v e eps loss mesh + overhead := by
  unfold scaleExponentTau arithmeticExponentTotal mixedSourceExponentTau
    sourceExponentTau realLossTau lxTau lyTau ellTau heightTau
  ring

lemma mixed_physical_exponent_total (Z ρ a v d R q e eps loss mesh overhead : ℝ)
    (N : ℕ) (hZ : 0 < Z) :
    ((Z ^ (lxTau ρ)) ^ (4 / 25 : ℝ) * Z ^ (a + 16 * e - 33 / 50) *
      (Z ^ (lyTau ρ)) ^ (-a - 6 * e)) *
      (Z ^ overhead * ((Z ^ d) ^ R * (Z ^ v) ^
        (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) *
        Z ^ ((ellTau ρ) * (-(4 / 25) + q + mesh) + loss))) =
      Z ^ (3 / 16 + mixedSourceExponentTau ρ a v d R q +
        realLossTau ρ N v e eps loss mesh + overhead) := by
  rw [shifted_physical_scale_identity Z ρ a e hZ]
  simp_rw [← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ]
  congr 1
  rw [← central_class_exponent_identity_total N ρ a v d R q e eps loss mesh overhead]
  unfold arithmeticExponentTotal
  ring

lemma realLossTau_bound_fixed (N : ℕ) (v e eps loss mesh : ℝ)
    (hv : v ≤ 1) (he : 0 ≤ e) (heps : 0 ≤ eps) (hmesh : 0 ≤ mesh) :
    realLossTau rho0 N v e eps loss mesh ≤
      26 * e + (N + 8) * eps + loss + totalE * mesh := by
  have hecoef : 16 - 6 * lyTau rho0 + 12 * v ≤ 26 := by
    unfold lyTau rho0
    linarith
  have h1 := mul_le_mul_of_nonneg_right hecoef he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0 ≤ eps * (N + 8) by positivity)
  unfold realLossTau
  rw [show ellTau rho0 = totalE by rfl]
  nlinarith

/-! One mixed exponent lemma matching the adaptive count actually returned by the count bridge. -/

def adaptiveRowExponentWide (δ q β ε εm slotMesh ν : ℝ) : ℝ :=
  if δ ≤ 5 / 6 then
    Endpoint.balancedRowCount δ (1 / 2 - q / δ) + deltaGap β / 4 +
      159 * ε + εm + slotMesh + 7 * ν
  else 1 - δ + 78 * ε + εm

/-- Lean's total division gives the explicit `δ = 0` convention used by the balanced formula. -/
lemma adaptiveRowExponentWide_zero_division_convention
    (q β ε εm slotMesh ν : ℝ) :
    adaptiveRowExponentWide 0 q β ε εm slotMesh ν =
      Endpoint.balancedRowCount 0 (1 / 2) + deltaGap β / 4 +
        159 * ε + εm + slotMesh + 7 * ν := by
  norm_num [adaptiveRowExponentWide]

lemma adaptive_mixed_saving_gap (N : ℕ)
    (a q β ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1 / 2 < a) (ha' : a ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ (2 * a - 1) / 2)
    (hβ0 : boundary < β) (hβ1 : β ≤ 1)
    (hε : 0 ≤ ε) (hεm : 0 ≤ εm) (hslot : 0 ≤ slotMesh) (hν : 0 ≤ ν)
    (hcount : 159 * ε + εm + slotMesh + 7 * ν ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hv : v ≤ physicalHeight + ζ) (hv1 : v ≤ 1)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ)
    (he : 0 ≤ e) (heps : 0 ≤ eps) (hmesh : 0 ≤ mesh)
    (hbudget : physicalHeight * (159 * ε + εm + slotMesh + 7 * ν) +
      2 * ζ + (3 / 2) * μ +
      (26 * e + (N + 8) * eps + loss + totalE * mesh) + overhead + saving +
      15 * rho0 / 8 ≤ 49 / 440640) :
    mixedSourceExponentTau rho0 a v d
        (adaptiveRowExponentWide (2 * a - 1) q β ε εm slotMesh ν) q +
      realLossTau rho0 N v e eps loss mesh + overhead ≤
        β - 7 / 8 - saving := by
  have hδ : 0 < 2 * a - 1 := by linarith
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hq hδ.le
  have hx' : q / (2 * a - 1) ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hL0 : 0 ≤ 159 * ε + εm + slotMesh + 7 * ν := by positivity
  have hreal := realLossTau_bound_fixed N v e eps loss mesh hv1 he heps hmesh
  by_cases hdlt : 2 * a - 1 ≤ 5 / 6
  · have hm := balanced_mixed_margin_gap (2 * a - 1) (q / (2 * a - 1)) β
      (159 * ε + εm + slotMesh + 7 * ν) ζ μ v d hδ.le hdlt hx hx'
      hβ0.le hβ1 hL0 hcount hζ hζ1 hv hμ hdv
    have hqeq : (2 * a - 1) * (q / (2 * a - 1)) = q := mul_div_cancel₀ q hδ.ne'
    have haeq : (1 + (2 * a - 1)) / 2 = a := by ring
    rw [haeq, hqeq] at hm
    dsimp only at hm
    unfold adaptiveRowCount at hm
    simp only [adaptiveRowExponentWide, if_pos hdlt]
    simp only [add_assoc] at hm ⊢
    linarith
  · have hLhigh0 : 0 ≤ 78 * ε + εm := by positivity
    have hLhigh1 : 78 * ε + εm ≤ 1 / 32 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 81 by norm_num) hε, hcount]
    have hm := high_mixed_margin_gap (2 * a - 1) q β (78 * ε + εm) ζ μ v d
      (le_of_lt (lt_of_not_ge hdlt)) (by linarith) hq hq' hβ0.le hLhigh0 hLhigh1
      hζ hζ1 hv hμ hdv
    have hHL : physicalHeight * (78 * ε + εm) ≤
        physicalHeight * (159 * ε + εm + slotMesh + 7 * ν) := by
      apply mul_le_mul_of_nonneg_left _ height_nonneg
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 81 by norm_num) hε]
    have haeq : (1 + (2 * a - 1)) / 2 = a := by ring
    rw [haeq] at hm
    simp only [adaptiveRowExponentWide, if_neg hdlt]
    simp only [add_assoc] at hm ⊢
    linarith

end SevenEighths.PerturbedCentral
end
end OAI
