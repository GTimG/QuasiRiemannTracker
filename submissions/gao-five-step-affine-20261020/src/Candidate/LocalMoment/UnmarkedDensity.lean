import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorCountFromMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint

/-! The unmarked zero-density source interface used by the proposed local
physical moment.  These lemmas use only the existing unmarked plain and
inverse moments.  They do not assert the local physical moment. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorBranchBudget HeckeDetectorRowCount
open HeckeDetectorInverseFiberCount
open HeckeDetectorRowwisePolynomial

def unmarkedDensity (δ : ℝ) : ℝ := 1 - 10 * δ / (3 * (5 - 2 * δ))

def unmarkedCutoff (δ : ℝ) : ℝ := Endpoint.balancedCutoff δ (1 / 2)

theorem unmarkedDensity_ge_two_sevenths {δ : ℝ} (hδ : δ ≤ 3 / 4) :
    2 / 7 ≤ unmarkedDensity δ := by
  have hden : 0 < 3 * (5 - 2 * δ) := by linarith
  have hquot : 10 * δ / (3 * (5 - 2 * δ)) ≤ 5 / 7 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  unfold unmarkedDensity
  linarith

theorem unmarkedCutoff_eq {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    unmarkedCutoff δ = 5 / (5 - 2 * δ) := by
  have hden : 5 - 2 * δ ≠ 0 := by linarith
  have hden' : (5 : ℝ) - δ * 2 ≠ 0 := by linarith
  have hD : Endpoint.balanceDenominator δ (1 / 2) = (5 - 2 * δ) / 2 := by
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
    ring
  unfold unmarkedCutoff Endpoint.balancedCutoff
  rw [hD, show 2 * ((5 - 2 * δ) / 2) = 5 - 2 * δ by ring]
  norm_num [Endpoint.primeWeight]
  field_simp [hden, hden']
  ring

theorem unmarkedDensity_eq_balanced {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    unmarkedDensity δ = Endpoint.balancedRowCount δ (1 / 2) := by
  have hden : 5 - 2 * δ ≠ 0 := by linarith
  have hden' : (5 : ℝ) - δ * 2 ≠ 0 := by linarith
  unfold Endpoint.balancedRowCount
  change unmarkedDensity δ = 1 - 5 / 6 + (5 / 6 - δ) * unmarkedCutoff δ
  rw [unmarkedCutoff_eq hδ]
  unfold unmarkedDensity
  field_simp [hden, hden']
  ring

theorem unmarkedCutoff_bounds {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6) :
    1 ≤ unmarkedCutoff δ ∧ unmarkedCutoff δ ≤ 3 / 2 := by
  simpa only [unmarkedCutoff, sub_zero] using
    balanced_cutoff_bounds hδ hδ' (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)

/-- Two existing unmarked source bounds suffice for the density exponent.
The support tolerance is kept explicitly; no prime amplitude or marked
moment is used in this interpolation. -/
theorem unmarked_count_bound (B C U δ r m ε γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (hγ : 0 ≤ γ)
    (hleft : unmarkedCutoff δ - r - γ ≤ m)
    (hright : r ≤ unmarkedCutoff δ + γ)
    (hI : B ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + ε))
    (hP : B ≤ C * U ^ (1 - 2 * δ * m + ε)) :
    B ≤ C * U ^ (unmarkedDensity δ + ε + 2 * γ) := by
  have hbounds := unmarkedCutoff_bounds hδ hδ'
  have hbal := balanced_count_identity hδ hδ'
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hbal' : max (shortExponent δ 0 (unmarkedCutoff δ))
      (longExponent δ (unmarkedCutoff δ)) = unmarkedDensity δ := by
    simpa only [unmarkedCutoff, sub_zero, ← unmarkedDensity_eq_balanced hδ'] using hbal
  have hs : shortExponent δ 0 (unmarkedCutoff δ) ≤ unmarkedDensity δ := by
    rw [← hbal']
    exact le_max_left _ _
  have hl : longExponent δ (unmarkedCutoff δ) ≤ unmarkedDensity δ := by
    rw [← hbal']
    exact le_max_right _ _
  have promote (p : ℝ) (hp : B ≤ C * U ^ p)
      (hpt : p ≤ unmarkedDensity δ + ε + 2 * γ) :
      B ≤ C * U ^ (unmarkedDensity δ + ε + 2 * γ) :=
    hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · rw [max_eq_right (show (1 : ℝ) ≤ (1 + 5 * r) / 6 by linarith)] at hI
    apply promote _ hI
    have hh := long_count_bound hδ' hγ hright
    have hg : (5 / 6 - δ) * γ ≤ 2 * γ := by nlinarith
    linarith
  · rw [max_eq_left (show (1 + 5 * r) / 6 ≤ (1 : ℝ) by linarith)] at hI
    have hchoose := selected_short_bound (δ := δ) (x := 0)
      (t := unmarkedCutoff δ) (r := r) hδ (by norm_num) (by norm_num)
    by_cases hrc : crossing 0 (unmarkedCutoff δ) ≤ r
    · apply promote _ hI
      have hh := hchoose.2 hrc
      unfold inverseExponent at hh
      nlinarith
    · apply promote _ hP
      have hh := hchoose.1 (le_of_not_ge hrc)
      have hm := mul_le_mul_of_nonneg_left hleft (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)
      have hg : 2 * δ * γ ≤ 2 * γ := by nlinarith
      unfold plainExponent at hh
      nlinarith

/-- A detector fiber with no required prime-slot supply.  Unlike the existing
marked `HeckeDetectorRawFiber.Fiber`, it admits a truly unmarked source. -/
structure UnmarkedFiber (U a ε tstar T allowance : ℝ) (i : ℕ) (Label : Type*) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow → Label → Character
  witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u ∈ rows, (witness u).label = label
  fixed_left : ∀ u ∈ rows, (witness u).left = left
  fixed_right : ∀ u ∈ rows, (witness u).right = right
  row_norm : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u ∈ rows, ∀ J : Ideal O, idealCoeff (family u label) J =
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val, u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val, u.property.1⟩) J

def UnmarkedFiber.r {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label) : ℝ :=
  Real.logb U ((2 : ℝ) ^ F.left.val)

def UnmarkedFiber.m {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label) : ℝ :=
  Real.logb U ((2 : ℝ) ^ F.right.val)

structure UnmarkedMoments {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      let W := twistProfile (logTest
        (orientedProfile F.reverse (inverseTest U tstar F.r)) n) s t
      RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  plain_unmarked : ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) s t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2 ≤
          C * U ^ (max 1 (2 * F.m) + εm)

/-- The actual unmarked detector density bound follows from the established
raw inverse moment and the established two-plain zero-slot moment.  The
statement retains coefficient orientation, all source profiles and frequencies,
and the full finite row set; its only loss is the displayed source padding. -/
theorem count_from_unmarked_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
        ∀ (a ε T allowance C height : ℝ) (i : ℕ),
        1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
        0 ≤ C → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
        ∀ {Label : Type*}
          (F : UnmarkedFiber U a ε (unmarkedCutoff (2 * a - 1)) T allowance i Label),
        UnmarkedMoments F c κ C height εm →
          (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
            U ^ (unmarkedDensity (2 * a - 1) + 156 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count M H hH S φ hφ hφc hφp hφ0
      hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance C height i hU ha hδcap hε hεsmall hC hh hf Label F moments
  let δ := 2 * a - 1
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have ht := unmarkedCutoff_bounds hδ hδcap
  have hgeom := fiber_lengths F.rows F.nonempty F.family U a ε (unmarkedCutoff δ)
    T allowance i hU F.witness F.left F.right F.fixed_left F.fixed_right
  change unmarkedCutoff δ - F.r - ε ≤ F.m ∧ F.r ≤ unmarkedCutoff δ + ε ∧
    F.m ≤ 1 / 2 + 75 * ε ∧ unmarkedCutoff δ - 1 / 2 - 76 * ε ≤ F.r ∧
    0 ≤ F.m at hgeom
  have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
  have hUp : 0 < U := zero_lt_one.trans hU
  obtain ⟨hconst, hconstP, hconstI, hconstI0⟩ :=
    fiberConstant_bounds C height K₀ hC hh hK
  have hi0 := hamp F.rows F.family a ε (unmarkedCutoff δ) T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf
    F.row_norm F.row_coeff moments.inverse_raw
  have hp0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count F.rows F.family U a ε
    (unmarkedCutoff δ) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right εm C height hC hh hf moments.plain_unmarked
  have promote (C' p q : ℝ) (hC' : C' ≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q) :
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ * U ^ q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hI : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (max 1 ((1 + 5 * F.r) / 6) - δ * F.r + (154 * ε + εm)) := by
    apply promote _ _ _ hconstI0 hi0
    change max 1 ((1 + 5 * F.r) / 6) - δ * F.r + 2 * ε + εm ≤
      max 1 ((1 + 5 * F.r) / 6) - δ * F.r + (154 * ε + εm)
    linarith
  have hP : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (1 - 2 * δ * F.m + (154 * ε + εm)) := by
    apply promote _ _ _ hconstP hp0
    change max 1 (2 * F.m) - 2 * δ * F.m + 4 * ε + εm ≤
      1 - 2 * δ * F.m + (154 * ε + εm)
    have hm : max 1 (2 * F.m) ≤ 1 + 150 * ε := max_le (by linarith) (by linarith [hgeom.2.2.1])
    linarith
  have hbound := unmarked_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀)
    U δ F.r F.m (154 * ε + εm) ε hconst hU.le hδ hδcap hε
    hgeom.1 hgeom.2.1 hI hP
  convert hbound using 1
  congr 2
  ring

end SevenEighths.LocalMoment
end
end OAI
