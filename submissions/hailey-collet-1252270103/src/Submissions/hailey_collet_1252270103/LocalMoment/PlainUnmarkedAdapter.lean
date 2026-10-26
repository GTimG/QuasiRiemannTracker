import Submissions.hailey_collet_1252270103.LocalMoment.UnmarkedDensity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCancellation

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentEnergyBands
open CenteredMomentEnergyState CenteredMomentDetectorPlainStateDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorPlainProfileControl
open ProbeDetectorPlainUnmarkedField QuadraticInitialBound ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/-- The conductor-bounded natural representative has exactly the coefficient
sequence used by the fixed raw/plain moment dictionary. -/
theorem natural_row_moment_dictionary (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1).character I =
      idealCoeff ((momentData η).character (momentElement u)) I := by
  rw [CenteredMomentNaturalRowSource.NaturalRow.ideal, momentData_coeff]
  have hm : CenteredMomentSecondHeightFamily.fixedBadMask = rowMaskElement := by
    unfold CenteredMomentSecondHeightFamily.fixedBadMask rowMaskElement
    ring
  rw [hm]

/-- A zero-profile auxiliary slot meets the legacy interface supply condition.
It has no analytic contribution: every use below selects the empty product.
No prime-slot lower bound on the input family is assumed. -/
def UnmarkedFiber.toLegacy {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) :
    Fiber M H Label Unit U a ε tstar T allowance i where
  rows := F.rows
  nonempty := F.nonempty
  family := F.family
  witness := F.witness
  label := F.label
  left := F.left
  right := F.right
  fixed_label := F.fixed_label
  fixed_left := F.fixed_left
  fixed_right := F.fixed_right
  row_norm := F.row_norm
  rowData := F.rowData
  reverse := F.reverse
  row_coeff := F.row_coeff
  slots := {()}
  profile := fun _ _ => 0
  upper := fun _ => 0
  widths := fun _ => 7 / 37
  external := fun _ => 0
  bin := fun _ => HeckePrimeAmplitudeBins.amplitude (U^(7/37:ℝ)) ((2*a-1)/2) 1 0
  mesh := 7 / 37
  binWidth := 1
  mesh_nonneg := by norm_num
  binWidth_pos := by norm_num
  widths_pos := by intros; norm_num
  widths_mesh := by intros; exact le_rfl
  supply := by simp
  fixed_bin := by
    intros
    simp [HeckeDetectorPhysicalSelection.physical, HeckePrimeRow.canonicalPrimeAmplitude]

/-- The actual retained plain estimate for an unmarked detector fiber. It
keeps the literal dictionary and eligible-row condition, so it cannot be used
for a different family merely because the scalar exponents agree. -/
theorem unmarked_retained_plain
    {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (Q : Ideal O) (δ e : ℝ)
    (hU : 1 < U) (hδ : 0 ≤ δ)
    (hwidth : max 1 (2 * F.m) + δ ≤ 2)
    (hm : F.m ≤ 1)
    (hη : (η.modulus.absNorm : ℝ) ≤ U^δ)
    (hdata : F.rowData = momentData η)
    (hMm : M ≤ Ideal.span {rowMaskElement})
    (hkeep : ∀ u ∈ F.rows, initialKeep η Q u.val)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (A : ℝ)
    (hzero : ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 e U degree S A)
    (j k : ℕ) (σ t : ℝ) :
    (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
      ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
      polynomial (F.family u F.label) false
      ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
      A * diagonalControl radialMajorant *
        (detectorProfiles F.reverse j k σ t).control S ^ 2 *
        U^(max 1 (2 * F.m) + δ + e) := by
  let G := F.toLegacy M H
  have hGM : G.m = F.m := rfl
  have hdataG : G.rowData = momentData η := hdata
  have hcompare := retained_positive_energy_le_source (initialKeep η Q)
    radialMajorant radialMajorant_nonneg radialMajorant_one G η ∅ j k σ t
    (zero_lt_one.trans hU) hkeep
  rw [← fiber_plain_unmarked_energy_eq G η hdataG hMm (zero_lt_one.trans hU) j k σ t]
    at hcompare
  let s := state G η Q radialMajorant radialSupportUpper δ hU.le hδ
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have he : s.width = max 1 (2 * F.m) + δ := by
    change 1 + CenteredMomentDetectorPlainUnmarkedState.allowance δ G.m = _
    rw [padded_width, hGM]
  have hscale : U^G.m ≤ U^(1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (hGM ▸ hm)
  have hb := hzero s rfl (he ▸ hwidth) (detectorProfiles G.reverse j k σ t)
    0 (U^G.m) (U^G.m) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) hscale hscale
  rw [actual_source_eq G η Q radialMajorant radialSupportUpper δ hU.le hδ
    radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t] at hcompare
  apply hcompare.trans
  have hrad : s.radial.profile = radialMajorant := rfl
  have hrev : G.reverse = F.reverse := rfl
  simpa only [he, hrad, hrev, norm_zero, add_zero, one_pow, mul_one] using hb

/-- The incumbent analytic induction supplies the zero-slot estimate itself.
The base character and fixed conductor are fixed before taking the scale limit.
The zero slot profile used here is only an argument of the incumbent certificate. -/
theorem fixed_zero_input (e : ℝ) (he : 0 < e)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Ideal O) [NeZero Q] (hQtop : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ × ℕ), ∀ η : Character,
      Q ≤ η.modulus → ∃ A : ℝ, 0 < A ∧ ∀ᶠ U : ℝ in atTop,
        ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 e U degree control A := by
  let κ : ℝ := max (3/4) (2 * HeckeZeroSupremum.beta - 1)
  have hκ : (3/4:ℝ) ≤ κ := le_max_left _ _
  have hκβ : 2 * HeckeZeroSupremum.beta - 1 ≤ κ := le_max_right _ _
  have hcert := CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Unit) Q ⊤ le_top (fun _ : ℝ => (0:ℂ))
    1 2 (1/4) (9/4) radialSupportUpper 0 1 0 0 2 κ e
    (by norm_num) (by simp) (by fun_prop)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    radialSupportUpper_spec.1 (by norm_num) (by norm_num) hκ he hβ hκβ
  obtain ⟨degree, control, h⟩ :=
    CenteredMomentEnergyCappedWidthInduction.certified_terminal (α := Unit)
      Q ⊤ le_top (fun _ : ℝ => (0:ℂ)) 2 (1/4) (9/4) radialSupportUpper
      0 1 0 0 2 κ e (by norm_num) (by norm_num) (by linarith) he hcert
  refine ⟨degree, control, ?_⟩
  intro η hQη
  have hi : internalQ Q η = Q := by
    unfold internalQ
    exact inf_eq_left.mpr hQη
  obtain ⟨A, B, hA, hB, hb⟩ := h η Q le_rfl (by simpa only [hi] using NeZero.ne Q)
    (by simpa only [hi] using hQtop) (by simpa only [hi] using hQ72)
  exact ⟨A, hA, hb.mono (fun U hU => by simpa only [hi] using hU.2.1)⟩

/-- Uniform retained unmarked field for an actual fixed inducing character.
The scale threshold is chosen before every height, row family, and dyadic fiber.
No prime-slot supply or assumed raw/plain moment appears in the inputs. -/
theorem fixed_retained_unmarked_plain (η : Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
    (εm : ℝ) (hεm : 0 < εm) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ {a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
        (F : UnmarkedFiber U a ε tstar T allowance i Label),
      F.m ≤ 3/4 → F.rowData = momentData η →
      (∀ u ∈ F.rows, initialKeep η Q u.val) →
      ∀ height : ℝ, 0 ≤ height → ∀ j k : ℕ, j + k ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
        C * (1 + height)^J * U^(max 1 (2 * F.m) + εm) := by
  let δ : ℝ := min (εm / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδcap : δ ≤ 1/4 := min_le_right _ _
  have hδbudget : δ + δ ≤ εm := by
    have hd : δ ≤ εm/4 := min_le_left _ _
    linarith
  obtain ⟨degree, control, hz⟩ := fixed_zero_input δ hδ hβ Q hQtop hQ72
  obtain ⟨A, hA, hzero⟩ := hz η hQη
  obtain ⟨J, Cp, hCp, hprofiles⟩ := paired_control control
  let C : ℝ := A * (1 + diagonalControl radialMajorant) * Cp
  have hdiag : 0 ≤ diagonalControl radialMajorant := diagonalControl_nonneg _
  have hC : 0 < C := mul_pos (mul_pos hA (by linarith)) hCp
  have hC' : A * diagonalControl radialMajorant * Cp ≤ C := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : diagonalControl radialMajorant ≤
        1 + diagonalControl radialMajorant) hA.le) hCp.le
  have hmod : ∀ᶠ U : ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ U^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  refine ⟨J, C, hC, ?_⟩
  filter_upwards [hzero, hmod, eventually_gt_atTop (1:ℝ)] with U hz hmU hU
  refine ⟨hU, ?_⟩
  intro a ε tstar T allowance i Label F hm hdata hkeep height hh j k hjk σ hσ t ht
  have hwidth : max 1 (2 * F.m) + δ ≤ 2 := by
    have hmax : max 1 (2 * F.m) ≤ 3/2 := max_le (by norm_num) (by linarith)
    linarith
  have hb := unmarked_retained_plain F (Ideal.span {rowMaskElement}) ⊤ η Q δ δ
    hU hδ.le hwidth (by linarith) hmU hdata le_rfl hkeep degree control A hz j k σ t
  have ht' : ‖t‖ ≤ height := by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp : (detectorProfiles F.reverse j k σ t).control control ^ 2 ≤
      Cp * (1 + height)^J := by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl ht') J) hCp.le
  have hpow : U^(max 1 (2 * F.m) + δ + δ) ≤ U^(max 1 (2 * F.m) + εm) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  apply hb.trans
  calc
    _ ≤ (A * diagonalControl radialMajorant * (Cp * (1 + height)^J)) *
        U^(max 1 (2 * F.m) + εm) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hp (mul_nonneg hA.le hdiag)
      · exact hpow
      · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
      · exact mul_nonneg (mul_nonneg hA.le hdiag) (mul_nonneg hCp.le (by positivity))
    _ = (A * diagonalControl radialMajorant * Cp) * (1 + height)^J *
        U^(max 1 (2 * F.m) + εm) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC' (by positivity)) (by positivity)

/-- The free sixth-power-reduced rows removed by `initialKeep` lie in a
fixed finite set. In particular they need not be discarded by imposing a
scale-dependent lower bound on every row. -/
theorem fixed_exceptional_free_finite (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQtop : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus) :
    {u : FreeRow | ¬initialKeep η Q u.val}.Finite := by
  have hfinite := HeckeExceptionalRows.rows_finite
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
    (fun P hP => UniqueFactorizationMonoid.prime_of_normalized_factor P
      (Multiset.mem_toFinset.mp hP))
  have hpre : {u : FreeRow | u.val ∈ HeckeExceptionalRows.rows
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset}.Finite :=
    hfinite.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro u hu
  have hex : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1) 1 u.val := by
    by_contra hn
    exact hu ⟨u.property.1, hn⟩
  exact fixed_inducing_free_support η Q hQ0 hQtop hQ72 hQη
    (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1)
    (mul_ne_zero CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hex

/-- A trivial one-row bound uniform in the character, both frequencies,
and the real parameter. This also covers principal and small-conductor rows. -/
theorem detector_plain_absolute :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character, ∀ n : ℕ, n ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t D : ℝ, 0 < D →
      ‖polynomial χ false ((logProfile^[n]) positiveAnnular) D σ t‖ ≤
        C * Real.sqrt D := by
  obtain ⟨A, hA, habs⟩ := detectorSchwartz_absolute
  refine ⟨128 * (9/4) * A, by positivity, ?_⟩
  intro χ n hn σ hσ t D hD
  have hs : Function.support (detectorSchwartz false n σ t : ℝ → ℂ) ⊆ Iic (9/4) :=
    fun x hx => (detectorSchwartz_support false n σ t hx).2
  have hp := CenteredMomentOriginalReflectionErrorMass.plain_polynomial_bound
    χ (detectorSchwartz false n σ t) (9/4) A D 0 hA.le hD
    (habs false n hn σ hσ t) hs
  have he : (detectorSchwartz false n σ t : ℝ → ℂ) =
      twistProfile ((logProfile^[n]) positiveAnnular) σ t := by
    funext x
    simpa only [HeckeDetectorCoefficientTransfer.orientedProfile,
      HeckeDetectorCoefficientTransfer.orientedFrequency, Bool.false_eq_true, ite_false]
      using detectorSchwartz_apply false n σ t x
  simpa only [he, polynomial_twistProfile, max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)] using hp

/-- A finite set of exceptional cores costs only its fixed cardinality times
D^2, within the zero-slot growth bound. -/
theorem finite_rows_plain_absolute :
    ∃ B : ℝ, 0 < B ∧ ∀ (rows : Finset FreeRow) (χ : FreeRow → Character),
      ∀ j k : ℕ, j + k ≤ 2 → ∀ σ ∈ Icc (0:ℝ) 1, ∀ t D : ℝ, 0 < D →
      (∑ u ∈ rows, ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) D σ t *
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) D σ t‖^2) ≤
        (rows.card : ℝ) * B * D^2 := by
  obtain ⟨C, hC, hb⟩ := detector_plain_absolute
  refine ⟨C^4, by positivity, ?_⟩
  intro rows χ j k hjk σ hσ t D hD
  have hp (u : FreeRow) : ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) D σ t *
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) D σ t‖^2 ≤ C^4 * D^2 := by
    have hj := hb (χ u) j (by omega) σ hσ t D hD
    have hk := hb (χ u) k (by omega) σ hσ t D hD
    rw [norm_mul]
    have hprod := mul_le_mul hj hk (norm_nonneg _) (by positivity : 0 ≤ C * Real.sqrt D)
    have hsq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hprod 2
    convert hsq using 1
    rw [mul_pow, mul_pow, Real.sq_sqrt hD.le]
    ring
  calc
    _ ≤ ∑ u ∈ rows, C^4 * D^2 := Finset.sum_le_sum (fun u _ => hp u)
    _ = _ := by simp; ring

/-- Complete zero-slot plain field, including all small and exceptional free
cores. The theorem has a common scale threshold for all heights and fibers.
Its inducing character is fixed and its row dictionary is literal. -/
theorem fixed_unmarked_plain (η : Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
    (εm : ℝ) (hεm : 0 < εm) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ {a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
        (F : UnmarkedFiber U a ε tstar T allowance i Label),
      F.m ≤ 3/4 → F.rowData = momentData η →
      ∀ height : ℝ, 0 ≤ height → ∀ j k : ℕ, j + k ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
        C * (1 + height)^J * U^(max 1 (2 * F.m) + εm) := by
  obtain ⟨J, C, hC, hret⟩ := fixed_retained_unmarked_plain η Q hQtop hQ72 hQη εm hεm hβ
  obtain ⟨B, hB, habs⟩ := finite_rows_plain_absolute
  let E : Finset FreeRow := (fixed_exceptional_free_finite η Q (NeZero.ne Q) hQtop hQ72 hQη).toFinset
  let K : ℝ := (E.card : ℝ) * B
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) hB.le
  refine ⟨J, C + K, by linarith, ?_⟩
  filter_upwards [hret] with U hret
  refine ⟨hret.1, ?_⟩
  intro a ε tstar T allowance i Label F hm hdata height hh j k hjk σ hσ t ht
  let keep : FreeRow → Prop := fun u => initialKeep η Q u.val
  let retained := F.rows.filter keep
  let discarded := F.rows.filter (fun u => ¬keep u)
  let value : FreeRow → ℝ := fun u => ‖polynomial (F.family u F.label) false
    ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
    polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2
  let P : ℝ := U^(max 1 (2 * F.m) + εm)
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_lt_one.trans hret.1).le _
  have hheight : 1 ≤ (1 + height)^J := one_le_pow₀ (by linarith)
  have hretained : (∑ u ∈ retained, value u) ≤ C * (1 + height)^J * P := by
    by_cases hne : retained.Nonempty
    · let G : UnmarkedFiber U a ε tstar T allowance i Label :=
        { F with
          rows := retained
          nonempty := hne
          fixed_label := by intro u hu; exact F.fixed_label u (Finset.mem_filter.mp hu).1
          fixed_left := by intro u hu; exact F.fixed_left u (Finset.mem_filter.mp hu).1
          fixed_right := by intro u hu; exact F.fixed_right u (Finset.mem_filter.mp hu).1
          row_norm := by intro u hu; exact F.row_norm u (Finset.mem_filter.mp hu).1
          row_coeff := by intro u hu; exact F.row_coeff u (Finset.mem_filter.mp hu).1 }
      exact hret.2 G hm hdata (fun u hu => (Finset.mem_filter.mp hu).2)
        height hh j k hjk σ hσ t ht
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sum_empty]
      exact mul_nonneg (mul_nonneg hC.le (by positivity)) hP
  have hsub : discarded ⊆ E := by
    intro u hu
    exact (Set.Finite.mem_toFinset _).mpr (Finset.mem_filter.mp hu).2
  have hcard : (discarded.card : ℝ) ≤ (E.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hpower : (U^F.m)^2 ≤ P := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hret.1).le]
    apply Real.rpow_le_rpow_of_exponent_le hret.1.le
    have hmax := le_max_right (1:ℝ) (2 * F.m)
    dsimp [P]
    linarith
  have hdiscarded : (∑ u ∈ discarded, value u) ≤ K * (1 + height)^J * P := by
    have hb := habs discarded (fun u => F.family u F.label) j k hjk σ hσ t (U^F.m)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hret.1) _)
    apply hb.trans
    calc
      _ ≤ K * P := mul_le_mul (mul_le_mul_of_nonneg_right hcard hB.le)
        hpower (sq_nonneg _) hK
      _ ≤ K * (1 + height)^J * P := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hK hheight) hP
  have hsplit : (∑ u ∈ F.rows, value u) =
      (∑ u ∈ retained, value u) + ∑ u ∈ discarded, value u :=
    (Finset.sum_filter_add_sum_filter_not F.rows keep value).symm
  change (∑ u ∈ F.rows, value u) ≤ (C + K) * (1 + height)^J * P
  rw [hsplit]
  calc
    _ ≤ C * (1 + height)^J * P + K * (1 + height)^J * P := add_le_add hretained hdiscarded
    _ = _ := by ring

#print axioms natural_row_moment_dictionary
#print axioms fixed_unmarked_plain
#print axioms detector_plain_absolute
#print axioms finite_rows_plain_absolute
#print axioms fixed_retained_unmarked_plain
#print axioms fixed_exceptional_free_finite
#print axioms fixed_zero_input
#print axioms UnmarkedFiber.toLegacy
#print axioms unmarked_retained_plain
end SevenEighths.LocalMoment
end
end OAI
