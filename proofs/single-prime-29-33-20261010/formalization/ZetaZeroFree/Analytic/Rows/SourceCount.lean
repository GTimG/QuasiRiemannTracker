import ZetaZeroFree.Analytic.Moments.Source
import ZetaZeroFree.Analytic.Moments.Unconditional
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import ZetaZeroFree.Analytic.Rows.Count
import ZetaZeroFree.Analytic.Rows.UniformProfiles
import OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
import OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotInverseCount
import OAI.NumberTheory.DirichletL.Detector.DetectorBatch
import OAI.NumberTheory.DirichletL.PrimeRows.DetectorReady
import OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

namespace ZetaZeroFree.Analytic.Rows

noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open scoped Classical BigOperators ContDiff
open Set Filter

/-- The plain fourth moment needed for an unmarked fiber; its exponent is one. -/
def PlainRawAt {Row Label : Type*} (rows : Finset Row) (χ : Row → Label → Character)
    (label : Label) (U m height ε C : ℝ) : Prop :=
  ∀ j k : ℕ, j + k ≤ 2 → ∀ σ ∈ Icc (0 : ℝ) 1, ∀ freq ∈ Icc (-height) height,
    ∑ u ∈ rows, ‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
      (U ^ m) σ freq * polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
      (U ^ m) σ freq‖ ^ 2 ≤ C * U ^ (1 + ε)

/-- Common supported witnesses, fixed after `t0`, turn two unmarked moments
into the new count exponent. Both energies are evaluated at their actual zeros. -/
theorem fiber_count_from_raw {Row Label : Type*}
    (rows : Finset Row) (χ : Row → Label → Character)
    (U a ε T allowance height εm Ci Cs : ℝ) (i : ℕ)
    (hU : 1 < U) (ha : 1 / 2 ≤ a) (hδu : 2 * a - 1 ≤ 5 / 6)
    (hε : 0 ≤ ε) (hCi : 0 ≤ Ci) (hCs : 0 ≤ Cs) (hh : 0 ≤ height)
    (hf : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height)
    (w : ∀ u, SupportedWitness (χ u) U a ε (t0 (2 * a - 1)) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hl : ∀ u ∈ rows, (w u).label = label)
    (hJ : ∀ u ∈ rows, (w u).left = J) (hK : ∀ u ∈ rows, (w u).right = K)
    (hMraw : ∀ n : ℕ, n ≤ 2 → ∀ σ ∈ Icc (0 : ℝ) 1,
      ∀ freq ∈ Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (χ u label) true
        ((logProfile^[n]) (inverseTest U (t0 (2 * a - 1))
          (Real.logb U ((2 : ℝ) ^ J.val))))
        (U ^ (Real.logb U ((2 : ℝ) ^ J.val))) σ freq‖ ^ 2 ≤
        Ci * U ^ (inverseExponent (Real.logb U ((2 : ℝ) ^ J.val)) + εm))
    (hSraw : PlainRawAt rows χ label U (Real.logb U ((2 : ℝ) ^ K.val)) height εm Cs) :
    (rows.card : ℝ) ≤ max (12 * (1 + height) * Ci) (192 * (1 + height) * Cs) *
      U ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm) := by
  let r := Real.logb U ((2 : ℝ) ^ J.val)
  let m := Real.logb U ((2 : ℝ) ^ K.val)
  let C := max (12 * (1 + height) * Ci) (192 * (1 + height) * Cs)
  have hC : 0 ≤ C := le_max_of_le_left (by positivity)
  by_cases hne : rows.Nonempty
  · have hlen := fiber_lengths rows hne χ U a ε (t0 (2 * a - 1)) T allowance i hU w J K hJ hK
    have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε (t0 (2 * a - 1))
      T allowance i hU (by linarith) (fun u => (w u).toWitness) label J K hl hJ hK
    have hUp : 0 < U := zero_lt_one.trans hU
    have hME := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε (t0 (2 * a - 1))
      T allowance i (by linarith) (fun u => (w u).toWitness) label
      (inverseTest U (t0 (2 * a - 1)) r) (U ^ r) (1 / 4) (9 / 4)
      (Ci * U ^ (inverseExponent r + εm)) (fun _ => 1)
      (Real.rpow_pos_of_pos hUp _) (by norm_num)
      (HeckeDetectorDyadicActual.inverse_profile_support _ _) (by positivity) height hh hf
      (by simpa only [mul_one] using hMraw)
    have hSE := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε (t0 (2 * a - 1))
      T allowance i (by linarith) (fun u => (w u).toWitness) label positiveAnnular (U ^ m)
      (1 / 4) (9 / 4) (Cs * U ^ (1 + εm)) (fun _ => 1)
      (Real.rpow_pos_of_pos hUp _) (by norm_num) positiveAnnular_support
      (by positivity) height hh hf (by simpa only [mul_one, PlainRawAt] using hSraw)
    simp only [mul_one] at hME hSE
    have hMi : ∑ u ∈ rows, ‖polynomial (χ u label) true
        (inverseTest U (t0 (2 * a - 1)) r) (U ^ r) (w u).zero.re (w u).frequency‖ ^ 2 ≤
        C * U ^ (inverseExponent r + εm) := by
      apply hME.trans
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hUp.le _)
    have hSi : ∑ u ∈ rows, ‖polynomial (χ u label) false positiveAnnular
        (U ^ m) (w u).zero.re (w u).frequency‖ ^ 4 ≤ C * U ^ (1 + εm) := by
      have he : ∑ u ∈ rows, ‖polynomial (χ u label) false positiveAnnular
          (U ^ m) (w u).zero.re (w u).frequency‖ ^ 4 ≤
          (192 * (1 + height) * Cs) * U ^ (1 + εm) := by
        simpa only [norm_mul, mul_pow, ← pow_add, show 2 + 2 = 4 by norm_num,
          mul_assoc] using hSE
      exact he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hUp.le _))
    have hc := card_bound_from_two_moments rows
      (fun u => polynomial (χ u label) true (inverseTest U (t0 (2 * a - 1)) r)
        (U ^ r) (w u).zero.re (w u).frequency)
      (fun u => polynomial (χ u label) false positiveAnnular (U ^ m)
        (w u).zero.re (w u).frequency)
      U (2 * a - 1) r m ε (2 * ε) εm C hU.le (by linarith) hδu hε
      (by positivity) hC hlen.2.1 (by linarith [hlen.1])
      (fun u hu => (hsp u hu).2.2.1) (fun u hu => (hsp u hu).2.2.2) hMi hSi
    convert hc using 1
    congr 2
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (zero_lt_one.trans hU).le _)


theorem plain_fiber_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row → Label → Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1 < U) (ha : 0 ≤ a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hl : ∀ u ∈ rows, (w u).label = label)
    (hJ : ∀ u ∈ rows, (w u).left = J) (hK : ∀ u ∈ rows, (w u).right = K)
    (εm C height : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height)
    (hraw : PlainRawAt rows χ label U (Real.logb U ((2 : ℝ) ^ K.val)) height εm C) :
    (rows.card : ℝ) ≤ (192 * (1 + height) * C) *
      U ^ (1 - 2 * (2 * a - 1) * Real.logb U ((2 : ℝ) ^ K.val) + 4 * ε + εm) := by
  let m := Real.logb U ((2 : ℝ) ^ K.val)
  have hUp : 0 < U := zero_lt_one.trans hU
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU ha
    w label J K hl hJ hK
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i ha
    w label positiveAnnular (U ^ m) (1 / 4) (9 / 4) (C * U ^ (1 + εm)) (fun _ => 1)
    (Real.rpow_pos_of_pos hUp _) (by norm_num) positiveAnnular_support (by positivity)
    height hh hf (by simpa only [PlainRawAt, mul_one] using hraw)
  simp only [mul_one] at he
  have hs (u : Row) (hu : u ∈ rows) : U ^ (2 * ((2 * a - 1) * m - 2 * ε)) ≤
      ‖polynomial (χ u label) false positiveAnnular (U ^ m) (w u).zero.re (w u).frequency *
        polynomial (χ u label) false positiveAnnular (U ^ m) (w u).zero.re (w u).frequency‖ ^ 2 := by
    rw [show 2 * ((2 * a - 1) * m - 2 * ε) = ((2 * a - 1) * m - 2 * ε) +
      ((2 * a - 1) * m - 2 * ε) by ring, Real.rpow_add hUp, norm_mul, mul_pow]
    exact mul_le_mul (hsp u hu).2.2.2 (hsp u hu).2.2.2 (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
  have he' : ∑ u ∈ rows, ‖polynomial (χ u label) false positiveAnnular (U ^ m)
      (w u).zero.re (w u).frequency * polynomial (χ u label) false positiveAnnular (U ^ m)
      (w u).zero.re (w u).frequency‖ ^ 2 ≤ (192 * (1 + height) * C) * U ^ (1 + εm) := by
    convert he using 1
    ring
  have hc := HeckeDetectorRowCount.card_of_energy rows _ U (2 * ((2 * a - 1) * m - 2 * ε))
    (1 + εm) (192 * (1 + height) * C) hUp hs he'
  convert hc using 1
  congr 2
  ring

 theorem fiber_count_from_counts {Row Label : Type*}
    (rows : Finset Row) (χ : Row → Label → Character)
    (U a ε T allowance εm Ci Cs : ℝ) (i : ℕ)
    (hU : 1 < U) (ha : 1 / 2 ≤ a) (hδu : 2 * a - 1 ≤ 5 / 6)
    (hε : 0 ≤ ε) (hCi : 0 ≤ Ci) (_hCs : 0 ≤ Cs)
    (w : ∀ u, SupportedWitness (χ u) U a ε (t0 (2 * a - 1)) T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u ∈ rows, (w u).left = J) (hK : ∀ u ∈ rows, (w u).right = K)
    (hMi : (rows.card : ℝ) ≤ Ci * U ^ (inverseExponent (Real.logb U ((2 : ℝ) ^ J.val)) -
      (2 * a - 1) * Real.logb U ((2 : ℝ) ^ J.val) + 2 * ε + εm))
    (hSi : (rows.card : ℝ) ≤ Cs * U ^ (1 - 2 * (2 * a - 1) *
      Real.logb U ((2 : ℝ) ^ K.val) + 4 * ε + εm)) :
    (rows.card : ℝ) ≤ max Ci Cs * U ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm) := by
  have hC : 0 ≤ max Ci Cs := le_max_of_le_left hCi
  by_cases hne : rows.Nonempty
  · let r := Real.logb U ((2 : ℝ) ^ J.val)
    let m := Real.logb U ((2 : ℝ) ^ K.val)
    have hlen := fiber_lengths rows hne χ U a ε (t0 (2 * a - 1)) T allowance i hU w J K hJ hK
    have hmin := unmarked_minimax (r := r) (m := m)
      (by linarith : 0 ≤ 2 * a - 1) hδu hε hlen.2.1
      (by linarith [hlen.1])
    by_cases hbranch : inverseExponent r - (2 * a - 1) * r ≤ 1 - 2 * (2 * a - 1) * m
    · rw [min_eq_left hbranch] at hmin
      exact hMi.trans (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)) (by positivity) hC)
    · rw [min_eq_right (le_of_not_ge hbranch)] at hmin
      exact hSi.trans (mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)) (by positivity) hC)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity


/-- The inverse input is supplied by the unconditional raw moment. Only the new
plain fourth moment remains an explicit analytic input. -/
theorem count_endpoint_from_plain
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ A : ℕ, ∀ data : RowData, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ {Label : Type*} (rows : Finset FreeRow) (χ : FreeRow → Label → Character)
        (a ε T allowance height Cs : ℝ) (i : ℕ),
      1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Cs → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ (w : ∀ u, SupportedWitness (χ u) U a ε (t0 (2 * a - 1)) T allowance i)
        (label : Label) (J K : Fin (dyadicLength U)),
      (∀ u ∈ rows, (w u).label = label) → (∀ u ∈ rows, (w u).left = J) →
      (∀ u ∈ rows, (w u).right = K) →
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      ∀ reverse : Bool,
      (∀ u ∈ rows, ∀ I : Ideal O, idealCoeff (χ u label) I =
        if reverse then starRingEnd ℂ (idealCoeff (data.character ⟨u.val, u.property.1⟩) I)
        else idealCoeff (data.character ⟨u.val, u.property.1⟩) I) →
      PlainRawAt rows χ label U (Real.logb U ((2 : ℝ) ^ K.val)) height εm Cs →
      (rows.card : ℝ) ≤ max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) *
        U ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, _, hκ, hK₀, hcount⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  obtain ⟨A, hraw⟩ := inverse_raw_pair_uniform c κ hc hκ
  refine ⟨A + 1, ?_⟩
  intro data
  obtain ⟨Cr, hCr, hraw⟩ := hraw data
  let C := 12 * Cr * K₀ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcount] with U hcount
  intro Label rows χ a ε T allowance height Cs i hU ha hδu hε hεsmall hCs hh hf
    w label J K hl hJ hK hrows reverse hcoeff hplain
  have hCi : 0 ≤ C * (1 + height) ^ (A + 1) := by positivity
  have hCp : 0 ≤ 192 * (1 + height) * Cs := by positivity
  by_cases hne : rows.Nonempty
  · have hlen := fiber_lengths rows hne χ U a ε (t0 (2 * a - 1)) T allowance i hU w J K hJ hK
    have ht := t0_range (by linarith : 0 ≤ 2 * a - 1) hδu
    have hr : 0 ≤ Real.logb U ((2 : ℝ) ^ J.val) := by linarith [hlen.2.2.2.1]
    have hr2 : Real.logb U ((2 : ℝ) ^ J.val) ≤ 2 := by linarith [hlen.2.1]
    have hi := hcount rows χ a ε (t0 (2 * a - 1)) T allowance i hU ha
      (fun u => (w u).toWitness) label J K hl hJ hK hr hr2 data reverse
      (Cr * (1 + height) ^ A) height (by positivity) hh hf hrows hcoeff
      (fun n hn σ hσ t ht => hraw reverse n hn U (zero_lt_one.trans hU)
        (t0 (2 * a - 1)) (Real.logb U ((2 : ℝ) ^ J.val)) σ hσ height t hh ht)
    have hfactor : 12 * (1 + height) * (Cr * (1 + height) ^ A * K₀) ≤
        C * (1 + height) ^ (A + 1) := by
      calc
        _ = (12 * Cr * K₀) * (1 + height) ^ (A + 1) := by rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    have hi' : (rows.card : ℝ) ≤ (C * (1 + height) ^ (A + 1)) *
        U ^ (inverseExponent (Real.logb U ((2 : ℝ) ^ J.val)) -
          (2 * a - 1) * Real.logb U ((2 : ℝ) ^ J.val) + 2 * ε + εm) :=
      hi.trans (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (zero_lt_one.trans hU).le _))
    have hp := plain_fiber_count rows χ U a ε (t0 (2 * a - 1)) T allowance i hU
      (by linarith) (fun u => (w u).toWitness) label J K hl hJ hK εm Cs height hCs hh hf hplain
    exact fiber_count_from_counts rows χ U a ε T allowance εm
      (C * (1 + height) ^ (A + 1)) (192 * (1 + height) * Cs) i hU ha hδu hε hCi hCp
      w J K hJ hK hi' hp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (le_max_of_le_left hCi) (Real.rpow_nonneg (zero_lt_one.trans hU).le _)


lemma plainRawAt_subset {Row Label : Type*} {small large : Finset Row}
    (hsub : small ⊆ large) (χ : Row → Label → Character) (label : Label)
    (U m height ε C : ℝ) (h : PlainRawAt large χ label U m height ε C) :
    PlainRawAt small χ label U m height ε C := by
  intro j k hjk σ hσ freq hf
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
    (h j k hjk σ hσ freq hf)

/-- Only presentations and dyads are classified; there are no prime-amplitude labels. -/
theorem family_count_endpoint_from_plain {Label : Type*} [Fintype Label]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ A : ℕ, ∀ data : Label → RowData, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (rows : Finset FreeRow) (χ : FreeRow → Label → Character)
        (a ε T allowance height Cs : ℝ) (i : ℕ),
      1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Cs → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ _w : ∀ u, SupportedWitness (χ u) U a ε (t0 (2 * a - 1)) T allowance i,
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      ∀ reverse : Label → Bool,
      (∀ u ∈ rows, ∀ label, ∀ I : Ideal O, idealCoeff (χ u label) I =
        if reverse label then starRingEnd ℂ (idealCoeff ((data label).character ⟨u.val, u.property.1⟩) I)
        else idealCoeff ((data label).character ⟨u.val, u.property.1⟩) I) →
      (∀ label m, 0 ≤ m → m ≤ 1 / 2 + 75 * ε → PlainRawAt rows χ label U m height εm Cs) →
      (rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) *
          U ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm) := by
  obtain ⟨A, hend⟩ := count_endpoint_from_plain M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨A, ?_⟩
  intro data
  choose Ci hCi hi using fun label => hend (data label)
  let C := 1 + ∑ label, Ci label
  have hsum : 0 ≤ ∑ label, Ci label := Finset.sum_nonneg (fun l _ => (hCi l).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have hbound (label : Label) : Ci label ≤ C := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => (hCi l).le)
      (Finset.mem_univ label)
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hi] with U hcount
  intro rows χ a ε T allowance height Cs i hU ha hδu hε hεsmall hCs hh hf w hrows reverse hcoeff hplain
  have hCmax : 0 ≤ max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) :=
    le_max_of_le_left (by positivity)
  apply le_trans (HeckeDetectorRowCount.classified_card_bound rows (fun u => (w u).label)
    (fun u => (w u).left.val) (fun u => (w u).right.val) (dyadicLength U)
    (fun u _ => (w u).left.isLt) (fun u _ => (w u).right.isLt)
    (max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) *
      U ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm)) ?_)
      (by simp only [mul_assoc]; exact le_rfl)
  intro label j hj k hk
  let J : Fin (dyadicLength U) := ⟨j, Finset.mem_range.mp hj⟩
  let K : Fin (dyadicLength U) := ⟨k, Finset.mem_range.mp hk⟩
  let R := rows.filter (fun u => (w u).label = label ∧ (w u).left.val = j ∧ (w u).right.val = k)
  have hsub : R ⊆ rows := Finset.filter_subset _ _
  have hl (u : FreeRow) (hu : u ∈ R) : (w u).label = label := (Finset.mem_filter.mp hu).2.1
  have hJ (u : FreeRow) (hu : u ∈ R) : (w u).left = J :=
    Fin.ext (Finset.mem_filter.mp hu).2.2.1
  have hK (u : FreeRow) (hu : u ∈ R) : (w u).right = K :=
    Fin.ext (Finset.mem_filter.mp hu).2.2.2
  by_cases hne : R.Nonempty
  · have hlen := fiber_lengths R hne χ U a ε (t0 (2 * a - 1)) T allowance i hU w J K hJ hK
    have hp := plainRawAt_subset hsub χ label U (Real.logb U ((2 : ℝ) ^ K.val)) height εm Cs
      (hplain label _ hlen.2.2.2.2 hlen.2.2.1)
    have hc := hcount label R χ a ε T allowance height Cs i hU ha hδu hε hεsmall hCs hh hf
      w label J K hl hJ hK (fun u hu => hrows u (hsub hu)) (reverse label)
      (fun u hu => hcoeff u (hsub hu) label) hp
    exact hc.trans (mul_le_mul_of_nonneg_right
      (max_le_max (mul_le_mul_of_nonneg_right (hbound label) (by positivity)) le_rfl)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _))
  · change (R.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hCmax (Real.rpow_nonneg (zero_lt_one.trans hU).le _)



lemma height_factor_bound (A B : ℕ) (height C Cp : ℝ)
    (hh : 0 ≤ height) (hC : 0 ≤ C) (hCp : 0 ≤ Cp) :
    max (C * (1 + height) ^ A) (192 * (1 + height) * (Cp * (1 + height) ^ B)) ≤
      (C + 192 * Cp) * (1 + height) ^ (A + B + 1) := by
  have hb : 1 ≤ 1 + height := by linarith
  apply max_le
  · exact mul_le_mul (by linarith) (pow_le_pow_right₀ hb (by omega)) (by positivity) (by positivity)
  · calc
      _ = (192 * Cp) * (1 + height) ^ (B + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul (by linarith) (pow_le_pow_right₀ hb (by omega)) (by positivity) (by positivity)

/-- Dyadic classification costs an arbitrarily small power, uniformly over the
moment shell. This exposes the loss consumed by the principal integral assembly. -/
theorem count_overhead_eventually {Label : Type*} [Fintype Label]
    (A B : ℕ) (dmin dmax q logLoss : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hq : 0 ≤ q) (hlog : 0 < logLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ C Cp exponent : ℝ, 0 ≤ C → 0 ≤ Cp →
      (Fintype.card Label : ℝ) * (dyadicLength (Z ^ d) : ℝ) ^ 2 *
        max (C * (1 + Z ^ q) ^ A) (192 * (1 + Z ^ q) * (Cp * (1 + Z ^ q) ^ B)) *
          (Z ^ d) ^ exponent ≤
      K * (C + 192 * Cp) * Z ^ (logLoss + q * (A + B + 1) + d * exponent) := by
  let ζ := logLoss / dmax
  obtain ⟨K₀, hK₀, hdyad⟩ := HeckeDetectorClassBudget.dyadic_cost_eventually ζ (by positivity)
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp hdyad
  refine ⟨(Fintype.card Label : ℝ) * K₀ * 2 ^ (A + B + 1), by positivity, ?_⟩
  filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin U₀ hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hscale hZ
  intro d hd hd' C Cp exponent hC hCp
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hdy := hU₀ (Z ^ d) (hscale d hd)
  have hqone : 1 ≤ Z ^ q := Real.one_le_rpow hZ hq
  have hheight : (1 + Z ^ q) ^ (A + B + 1) ≤
      2 ^ (A + B + 1) * Z ^ (q * (A + B + 1)) := by
    calc
      _ ≤ (2 * Z ^ q) ^ (A + B + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hZp.le]
        norm_num
  have hcost : (Z ^ d) ^ ζ ≤ Z ^ logLoss := by
    rw [← Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hh := mul_le_mul_of_nonneg_right hd' (show 0 ≤ ζ by positivity)
    have he : dmax * ζ = logLoss := by dsimp [ζ]; field_simp
    linarith
  have he := height_factor_bound A B (Z ^ q) C Cp (by positivity) hC hCp
  calc
    _ ≤ (Fintype.card Label : ℝ) * (K₀ * Z ^ logLoss) *
        ((C + 192 * Cp) * (2 ^ (A + B + 1) * Z ^ (q * (A + B + 1)))) *
        (Z ^ d) ^ exponent := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hdy.trans (mul_le_mul_of_nonneg_left hcost hK₀)) (Nat.cast_nonneg _))
        (he.trans (mul_le_mul_of_nonneg_left hheight (by positivity)))
        (le_max_of_le_left (by positivity)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul hZp.le, Real.rpow_add hZp, Real.rpow_add hZp]
      ring

open ProbeHighRowFamily ProbePhysical

def sourceFixedCore (S : Finset (Ideal O)) : Ideal O :=
  (∏ P ∈ S, P) ⊓ Ideal.span {(72 : O)}

lemma sourceFixedCore_ne_zero (S : Finset (Ideal O)) (hS : SourceExclusions S) :
    sourceFixedCore S ≠ 0 :=
  Ideal.inf_ne_bot_of_ne_bot
    (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS.prime P hP).ne_zero))
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0))

lemma sourceFixedCore_ne_top (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀ P ∈ S, P.IsMaximal) : sourceFixedCore S ≠ ⊤ := by
  have hmem : Ideal.span {ConcretePrimeRowBridge.goodLambda} ∈ S := by
    apply hS.bad
    change _ ∈ ({Ideal.span {ConcretePrimeRowBridge.goodLambda}, Ideal.span {(2 : O)}} : Finset (Ideal O))
    simp
  have hle : (∏ P ∈ S, P) ≤ Ideal.span {ConcretePrimeRowBridge.goodLambda} :=
    Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P : Ideal O => P) hmem)
  intro h
  exact (hmax _ hmem).isPrime.ne_top
    (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedCore S ≤ _)))

/-- A principal natural row would be a fixed inducing row. Its sixth-power-free
numerator has bounded norm, so it disappears from every growing lower shell. -/
theorem natural_nonprincipal_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character) (δlo : ℝ) (hδlo : 0 < δlo) :
    ∀ᶠ Z : ℝ in atTop, ∀ u : FreeRow, Z ^ δlo ≤ rowNorm u →
      (Moments.naturalPlainCharacter η u.val).residue ≠ 1 := by
  let Q := CenteredMomentNaturalFixedRaySource.internalQ (sourceFixedCore S) η
  have hQ0 : Q ≠ 0 := CenteredMomentNaturalFixedRaySource.internalQ_ne_zero _
    (sourceFixedCore_ne_zero S hS) η
  have hQtop : Q ≠ ⊤ := CenteredMomentNaturalFixedRaySource.internalQ_ne_top _
    (sourceFixedCore_ne_top S hS hmax) η
  have hQ72 : Q ≤ Ideal.span {(72 : O)} := inf_le_left.trans inf_le_right
  have hQη : Q ≤ η.modulus := inf_le_right
  let bound := HeckeExceptionalRows.bound (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  filter_upwards [(tendsto_rpow_atTop hδlo).eventually (eventually_gt_atTop (bound : ℝ))]
    with Z hZ
  intro u hu hprincipal
  let F := CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1
  have hp : F.character.residue = 1 := by
    rw [Moments.naturalPlainCharacter, dite_eq_left u.property.1] at hprincipal
    exact hprincipal
  have hex := CenteredMomentNonprincipalGate.principal_row_fixed η F.character Q
    CenteredMomentSecondHeightFamily.fixedBadMask 1 u.val
    (by simpa only [one_mul] using F.element) hp
  have hs := CenteredMomentNaturalFixedRaySource.fixed_inducing_free_support η Q
    hQ0 hQtop hQ72 hQη CenteredMomentSecondHeightFamily.fixedBadMask
    CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _) u hex
  have hn : rowNorm u ≤ (bound : ℝ) := by
    change ((Ideal.span {u.val}).absNorm : ℝ) ≤
      (HeckeExceptionalRows.bound (UniqueFactorizationMonoid.normalizedFactors Q).toFinset : ℝ)
    exact_mod_cast HeckeExceptionalRows.row_norm_bound _
      (fun P hP => UniqueFactorizationMonoid.prime_of_normalized_factor P
        (Multiset.mem_toFinset.mp hP)) hs
  exact (not_lt_of_ge (hu.trans hn)) hZ

section Source
open ProbeHighRowFamily ProbePhysical
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
local instance : Fintype (Sum Bool (RayQuotient.Characters M H)) := Fintype.ofFinite _

def SourcePlainAt (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (η : Character)
    (rows : Finset FreeRow) (U ε height εm C : ℝ) : Prop :=
  ∀ label m, 0 ≤ m → m ≤ 1 / 2 + 75 * ε →
    PlainRawAt rows (fun u => sourceDetectorFamily S hS η u (rayCubeFamily M H hH u))
      label U m height εm C

/-- One common natural-state endpoint fixes the height order before the target
character. Its finitely many fixed conductors only alter the eventual threshold. -/
theorem source_plain_from_all_nonprincipal
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (Φ : SchwartzMap ℝ ℂ) (radial dmin δlo ε δ loss εm C : ℝ)
    (J : ℕ) (control : Finset (ℕ × ℕ))
    (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Iic radial)
    (hΦp : ∀ x, 0 ≤ (Φ x).re) (hΦ1 : ∀ x ∈ Icc (0 : ℝ) 1, Φ x = 1)
    (hdmin : 0 < dmin) (hδlo : 0 < δlo) (hε : ε ≤ 1 / 1000)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C) (hbudget : δ + loss ≤ εm)
    (hend : ∀ᶠ U : ℝ in atTop,
      Moments.AllNonprincipalAt (1 / 4) (9 / 4) radial 0 1 2 loss U J control C) :
    ∃ B : ℕ, ∃ Cp : ℝ, 0 < Cp ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, Z ^ δlo ≤ rowNorm u) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ d) → ∀ height : ℝ, 0 ≤ height →
      SourcePlainAt M H hH S hS.prime η rows (Z ^ d) ε height εm
        (Cp * (1 + height) ^ B) := by
  obtain ⟨B, Cp₀, hCp₀, hprofiles⟩ := plain_profile_control control
  let Cp := C * (1 + QuadraticInitialBound.diagonalControl Φ) * Cp₀
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hCp : 0 < Cp := mul_pos (mul_pos hC (by linarith)) hCp₀
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hend
  refine ⟨B, Cp, hCp, ?_⟩
  intro η
  let base := CenteredMomentDetectorDictionary.sourceMomentBase M H hH S hS.prime η
  have hnorm : ∀ᶠ Z : ℝ in atTop, ∀ label,
      ((base label).modulus.absNorm : ℝ) ≤ Z ^ (dmin * δ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos hdmin hδ)).eventually (eventually_ge_atTop _)
  have hnonprincipal : ∀ᶠ Z : ℝ in atTop, ∀ label, ∀ u : FreeRow,
      Z ^ δlo ≤ rowNorm u → (Moments.naturalPlainCharacter (base label) u.val).residue ≠ 1 := by
    apply Filter.eventually_all.mpr
    intro label
    exact natural_nonprincipal_eventually S hS hmax (base label) δlo hδlo
  filter_upwards [hnorm, hnonprincipal,
    HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin (max 1 U₀) hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hnorm hnp hscale hZ
  intro d hd rows hlo hhi height hh label m hm hm' j k hjk σ hσ t ht
  have hU : 1 ≤ Z ^ d := (le_max_left _ _).trans (hscale d hd)
  have hmod : ((base label).modulus.absNorm : ℝ) ≤ (Z ^ d) ^ δ := by
    rw [← Real.rpow_mul (zero_lt_one.trans_le hZ).le]
    exact (hnorm label).trans (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul_of_nonneg_right hd hδ.le))
  have he := Moments.finite_plain_bound rows
    (fun u => sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) label)
    (base label) (sourceMomentReverse M H label) Φ radial (Z ^ d) δ m 1 2 loss C J control
    hU hδ.le hΦs hΦp hΦ1 hmod hhi (fun u hu => hnp label u (hlo u hu))
    (fun u _ I => Moments.source_natural_coefficient M H hH S hS.prime hS.bad η u label I)
    (by linarith) (by linarith) (hU₀ (Z ^ d) ((le_max_right _ _).trans (hscale d hd))) j k σ t
  apply he.trans
  apply mul_le_mul
  · calc
      _ ≤ (C * QuadraticInitialBound.diagonalControl Φ) * (Cp₀ * (1 + height) ^ B) :=
        mul_le_mul_of_nonneg_left (hprofiles (sourceMomentReverse M H label) j k hjk σ hσ height t hh ht)
          (mul_nonneg hC.le hdiag)
      _ ≤ (C * (1 + QuadraticInitialBound.diagonalControl Φ)) * (Cp₀ * (1 + height) ^ B) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC.le) (by positivity)
      _ = Cp * (1 + height) ^ B := by dsimp [Cp]; ring
  · exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  · positivity
  · positivity

/-- The actual zero-slot endpoint supplies all source rows with common profile
orders. The anchor is fixed independently of the target character. -/
theorem source_plain
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (hcore : sourceFixedCore S ≤ M)
    (Φ : SchwartzMap ℝ ℂ) (radial dmin δlo ε δ loss εm : ℝ)
    (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Iic radial)
    (hΦp : ∀ x, 0 ≤ (Φ x).re) (hΦ1 : ∀ x ∈ Icc (0 : ℝ) 1, Φ x = 1)
    (hradial : 0 < radial) (hdmin : 0 < dmin) (hδlo : 0 < δlo) (hε : ε ≤ 1 / 1000)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hloss : 0 < loss) (hbudget : δ + loss ≤ εm) :
    ∃ B : ℕ, ∃ Cp : ℝ, 0 < Cp ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, Z ^ δlo ≤ rowNorm u) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ d) → ∀ height : ℝ, 0 ≤ height →
      SourcePlainAt M H hH S hS.prime η rows (Z ^ d) ε height εm
        (Cp * (1 + height) ^ B) := by
  let anchor := fixedSourcePrincipal S hS.prime
  obtain ⟨J, control, C, hC, hend⟩ := Moments.Unconditional.all_nonprincipal_at M
    (1 / 4) (9 / 4) radial 0 1 2 loss (by norm_num) (by norm_num) (by norm_num)
    hradial (by norm_num) (by norm_num) hloss anchor (sourceFixedCore S) hcore
    (CenteredMomentNaturalFixedRaySource.internalQ_ne_zero _ (sourceFixedCore_ne_zero S hS) anchor)
    (CenteredMomentNaturalFixedRaySource.internalQ_ne_top _ (sourceFixedCore_ne_top S hS hmax) anchor)
    (inf_le_left.trans inf_le_right)
  exact source_plain_from_all_nonprincipal M H hH S hS hmax Φ radial dmin δlo ε δ loss εm C
    J control hΦs hΦp hΦ1 hdmin hδlo hε hδ hδ1 hC hbudget (hend.mono fun _ h => h.2)

/-- The actual source rows retain their full coefficient presentations. The
cutoff `t0` is fixed before the common zero and the two dyads are selected. -/
theorem actual_source_count_uniform_order
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (dmin dmax δlo ε e κ heightCost margin εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hδlo : 0 < δlo)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1000) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hheightCost : 0 ≤ heightCost)
    (hmargin : 0 < margin) (hεm : 0 < εm)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∃ A : ℕ, ∀ I : ℕ, ∀ τ : ℝ, 0 < τ → τ < dmin / 2 → 4 * τ < dmin * heightCost →
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ (physicalUpper a height Cs : ℝ)
        (rows : Finset FreeRow), rows ⊆ rowBand (Z ^ δlo) physicalUpper →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
      ∀ i : ℕ, i ≤ I → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
      0 ≤ height → 0 ≤ Cs →
      2 * Real.pi * (Z ^ d) ^ (τ / (2 * dmax)) + (3 * i : ℕ) * Z ^ τ ≤ height →
      SourcePlainAt M H hH S hS.prime η rows (Z ^ d) ε height εm Cs →
      (rows.card : ℝ) ≤ (Fintype.card (Sum Bool (RayQuotient.Characters M H)) : ℝ) *
        (dyadicLength (Z ^ d) : ℝ) ^ 2 *
        max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) *
          (Z ^ d) ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm) := by
  obtain ⟨A, hend⟩ := family_count_endpoint_from_plain
    (Label := Sum Bool (RayQuotient.Characters M H)) M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨A, ?_⟩
  intro I τ hτ hτzero hτheight
  obtain ⟨Z₀, hw⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  intro η
  obtain ⟨C, hC, hcount⟩ := hend (sourceMomentData M H hH S hS.prime η)
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp hcount
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin (max 2 U₀) hdmin,
    source_ray_nonprincipal_eventually M H hH S hS hmax η δlo hδlo,
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin,
    eventually_gt_atTop (1 : ℝ)] with Z hZ₀ hscale hnp hcond hZ
  intro d hd hd' physicalUpper a height Cs rows hrows hcal hrow i hi ha hδu hnext hcurrent hh hCs hf hplain
  have hU : 1 < Z ^ d := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_left _ _).trans (hscale d hd))
  have hnorm (u : FreeRow) (hu : u ∈ rows) : rowNorm u ≤ Z ^ d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  by_cases hne : rows.Nonempty
  · let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
    have hχ : ∀ u j, (χ u j).residue ≠ 1 := fun u =>
      hnp physicalUpper u.val (hrows u.property) (hcal u.val u.property)
    have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
    obtain ⟨w⟩ := hw Z hZ₀ d hd hd' χ hχ a i hi ha (by linarith)
      (fun u => by rw [← heq u]; exact hnext u.val u.property)
      (fun u => by rw [← heq u]; exact hcurrent u.val u.property)
      (fun u => hcond u.val d (hrow u.val u.property)) (t0 (2 * a - 1))
      (t0_range (by linarith) hδu).1 (t0_range (by linarith) hδu).2
    obtain ⟨u₀, hu₀⟩ := hne
    let χR := fun u : FreeRow => sourceDetectorFamily S hS.prime η
      (retainedProjection rows u₀ u) (rayCubeFamily M H hH (retainedProjection rows u₀ u))
    let wR : ∀ u, SupportedWitness (χR u) (Z ^ d) a ε (t0 (2 * a - 1))
        (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i :=
      fun u => w ⟨retainedProjection rows u₀ u, retainedProjection_mem rows u₀ hu₀ u⟩
    have hp : ∀ label m, 0 ≤ m → m ≤ 1 / 2 + 75 * ε →
        PlainRawAt rows χR label (Z ^ d) m height εm Cs := by
      intro label m hm hm' j k hjk σ hσ freq hfreq
      have hh' := hplain label m hm hm' j k hjk σ hσ freq hfreq
      apply le_trans _ hh'
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro u hu
      simp only [χR, retainedProjection_of_mem rows u₀ u hu]
    exact hU₀ (Z ^ d) ((le_max_right _ _).trans (hscale d hd)) rows χR a ε
      (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) height Cs i hU (by linarith) hδu hε.le hεsmall
      hCs hh hf wR hnorm (sourceMomentReverse M H)
      (by intro u hu label J; simp only [χR, retainedProjection_of_mem rows u₀ u hu]
          exact source_family_moment_coeff M H hH S hS.prime hS.bad η u label J) hp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (le_max_of_le_left (by positivity))) (Real.rpow_nonneg (zero_lt_one.trans hU).le _)

/-- Compatibility interface for callers whose height cell has already been fixed. -/
theorem actual_source_count_from_plain
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (dmin dmax δlo τ ε e κ heightCost margin εm : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hδlo : 0 < δlo) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1000) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hheightCost : 0 ≤ heightCost)
    (hmargin : 0 < margin) (hεm : 0 < εm)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∃ A : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ (physicalUpper a height Cs : ℝ)
        (rows : Finset FreeRow), rows ⊆ rowBand (Z ^ δlo) physicalUpper →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
      ∀ i : ℕ, i ≤ I → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
      0 ≤ height → 0 ≤ Cs →
      2 * Real.pi * (Z ^ d) ^ (τ / (2 * dmax)) + (3 * i : ℕ) * Z ^ τ ≤ height →
      SourcePlainAt M H hH S hS.prime η rows (Z ^ d) ε height εm Cs →
      (rows.card : ℝ) ≤ (Fintype.card (Sum Bool (RayQuotient.Characters M H)) : ℝ) *
        (dyadicLength (Z ^ d) : ℝ) ^ 2 *
        max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) *
          (Z ^ d) ^ (Exponent.R0 (2 * a - 1) + 6 * ε + εm) := by
  obtain ⟨A, hA⟩ := actual_source_count_uniform_order M H hH S hS hmax
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    dmin dmax δlo ε e κ heightCost margin εm hdmin hdmax hδlo hε hεsmall
    he he' hκ hκ' hheightCost hmargin hεm hbudget
  exact ⟨A, hA I τ hτ hτzero hτheight⟩

end Source

end
end ZetaZeroFree.Analytic.Rows
