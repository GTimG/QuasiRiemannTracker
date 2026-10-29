/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected-amplitude gap 1/10^9; original slots, masks, ordinary sources
and early mesh order are retained. Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FrontierDetectorWords
import Candidate.Local.Qrh.JointDetector.CountBuffers
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDynamicSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CenteredExceptionalCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
import Submissions.hailey_collet_1252270103.Cycle61.Density.ExceptionalLift

/-!
# Uniform joint detector count

This module assembles the actual OAI detector words. The selected all-source
operator bound remains an explicit input; no zero-count conclusion is an input.
The dictionary is finite and fixed, and the detector uses free core characters.
Moving sixth-root masks belong to the slot coefficients, not to its conductor.
-/
namespace Qrh.JointDetector.FrontierDetectorCount
open FrontierDetectorWords
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorProfiles
open HeckeDetectorDyadicProfiles HeckeDetectorRowwisePolynomial
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
local notation "O" => ActualEisensteinCubic.O

/-- A complete finite ordinary annular source family, including units and
repeated prime factors. Only the zero ideal is absent. -/
def detectorSources (D : ℝ) : Finset (Ideal O) := idealsUpTo ⌊(9/4)*D⌋₊

theorem mem_detectorSources {D : ℝ} {I : Ideal O} :
    I ∈ detectorSources D ↔ I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ (9/4)*D := by
  rw [detectorSources, mem_idealsUpTo]
  constructor
  · rintro ⟨hpos, hbound⟩
    have hn : I ≠ ⊥ := by
      intro hz
      subst I
      simp at hpos
    refine ⟨hn, ?_⟩
    have hfloor : (⌊(9/4)*D⌋₊ : ℝ) ≤ (9/4)*D := by
      apply Nat.floor_le
      have : 1 ≤ (⌊(9/4)*D⌋₊ : ℝ) := by exact_mod_cast hpos.trans hbound
      by_contra h
      have hz := Nat.floor_eq_zero.mpr (show (9/4)*D < 1 by linarith)
      simp only [hz, Nat.cast_zero] at this
      linarith
    exact (show (I.absNorm : ℝ) ≤ (⌊(9/4)*D⌋₊ : ℝ) by exact_mod_cast hbound).trans hfloor
  · rintro ⟨hI, hbound⟩
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),
      Nat.le_floor hbound⟩

theorem detectorSources_cover (W : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hs : Function.support W ⊆ Set.Icc (1/4 : ℝ) (9/4)) :
    ∀ I : Ideal O, I ≠ 0 → W ((I.absNorm : ℝ)/D) ≠ 0 → I ∈ detectorSources D := by
  intro I hI hW
  apply mem_detectorSources.mpr
  exact ⟨hI, (div_le_iff₀ hD).mp (hs hW).2 |>.trans_eq (by ring)⟩

theorem detectorSources_product_nonzero {D N : ℝ} {I : Ideal O}
    (hI : I ∈ idealProductSources (detectorSources D) (detectorSources N)) : I ≠ ⊥ := by
  obtain ⟨J, hJ, K, hK, rfl⟩ := (mem_idealProductSources _ _ _).mp hI
  exact mul_ne_zero (mem_detectorSources.mp hJ).1 (mem_detectorSources.mp hK).1

theorem detectorSources_product_norm {D N : ℝ} (hD : 0 ≤ D) (_hN : 0 ≤ N)
    {I : Ideal O} (hI : I ∈ idealProductSources (detectorSources D) (detectorSources N)) :
    (I.absNorm : ℝ) ≤ 6*(D*N) := by
  obtain ⟨J, hJ, K, hK, rfl⟩ := (mem_idealProductSources _ _ _).mp hI
  rw [map_mul, Nat.cast_mul]
  have h := mul_le_mul (mem_detectorSources.mp hJ).2 (mem_detectorSources.mp hK).2
    (Nat.cast_nonneg _) (by positivity : 0 ≤ (9/4)*D)
  nlinarith

theorem iterated_logProfile_eq (W : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    (logProfile^[n]) W x = (Real.log x : ℂ)^n * W x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', logProfile, ih, pow_succ]
      ring

theorem iterated_logProfile_support (W : ℝ → ℂ) (n : ℕ) :
    Function.support ((logProfile^[n]) W) ⊆ Function.support W := by
  intro x hx hW
  exact hx (by rw [iterated_logProfile_eq, hW, mul_zero])

/-- A uniform bound for all actual Sobolev profiles, independent of either
dyadic scale and of the terminal `U^21` tail. -/
theorem exists_actual_detector_profile_bound : ∃ L : ℝ, 1 ≤ L ∧
    (∀ n : ℕ, n ≤ 2 → Function.support ((logProfile^[n]) positiveAnnular) ⊆
      Set.Icc (1/4 : ℝ) (9/4) ∧ ∀ x, ‖(logProfile^[n]) positiveAnnular x‖ ≤ L) ∧
    (∀ (n : ℕ) (Dstar D : ℝ), n ≤ 2 →
      Function.support ((logProfile^[n]) (inverseProfile cutoff positiveAnnular Dstar D)) ⊆
        Set.Icc (1/4 : ℝ) (9/4) ∧
      ∀ x, ‖(logProfile^[n]) (inverseProfile cutoff positiveAnnular Dstar D) x‖ ≤ L) := by
  let C := |Real.log (1/4 : ℝ)| + |Real.log (9/4 : ℝ)|
  let L := 2*(1+C)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 1 ≤ L := by dsimp [L]; nlinarith
  have hann (x : ℝ) : ‖positiveAnnular x‖ ≤ 2 := by
    by_cases hx : 0 ≤ x
    · rw [positiveAnnular_eq x hx]
      change ‖cutoff x-cutoff (2*x)‖ ≤ 2
      have h := (norm_sub_le _ _).trans (add_le_add (cutoff_norm_le x) (cutoff_norm_le (2*x)))
      linarith
    · have hz : positiveAnnular x = 0 := by
        by_contra h
        have := (positiveAnnular_support h).1
        linarith
      simp only [hz, norm_zero]
      norm_num
  have hlog (x : ℝ) (hx : x ∈ Set.Icc (1/4 : ℝ) (9/4)) : |Real.log x| ≤ C := by
    have hxpos : 0 < x := by linarith [hx.1]
    have hlo := Real.log_le_log (by norm_num : 0 < (1/4 : ℝ)) hx.1
    have hhi := Real.log_le_log hxpos hx.2
    dsimp [C]
    have h0 := neg_abs_le (Real.log (1/4 : ℝ))
    have h1 := le_abs_self (Real.log (9/4 : ℝ))
    have h2 := abs_nonneg (Real.log (1/4 : ℝ))
    have h3 := abs_nonneg (Real.log (9/4 : ℝ))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hgeneric (W : ℝ → ℂ) (hs : Function.support W ⊆ Set.Icc (1/4 : ℝ) (9/4))
      (hW : ∀ x, ‖W x‖ ≤ 2) (n : ℕ) (hn : n ≤ 2) :
      Function.support ((logProfile^[n]) W) ⊆ Set.Icc (1/4 : ℝ) (9/4) ∧
      ∀ x, ‖(logProfile^[n]) W x‖ ≤ L := by
    refine ⟨(iterated_logProfile_support W n).trans hs, ?_⟩
    intro x
    rw [iterated_logProfile_eq]
    by_cases hx : W x = 0
    · simp only [hx, mul_zero, norm_zero]
      exact zero_le_one.trans hL
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp : |Real.log x|^n ≤ (1+C)^2 :=
      (pow_le_pow_left₀ (abs_nonneg _) ((hlog x (hs hx)).trans (by linarith)) n).trans
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1+C) hn)
    exact (mul_le_mul hp (hW x) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [L]; ring)
  refine ⟨L, hL, fun n hn => hgeneric positiveAnnular positiveAnnular_support hann n hn, ?_⟩
  intro n Dstar D hn
  apply hgeneric _ (HeckeDetectorDyadicActual.inverse_profile_support Dstar D) _ n hn
  intro x
  rw [HeckeDetectorDyadicBridge.inverseProfile, norm_mul]
  exact (mul_le_mul (cutoff_norm_le _) (hann x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)

/-- Scalar specialization of the genuine all-source norm input at any word
length between zero and three. Its source cap is `6 U^3`. -/
theorem selectedNorm_word_bound (rows : Finset O) (S : Finset (Ideal O))
    (U δ K Xmax w : ℝ) (hU : 1 ≤ U) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 3)
    (hbound : SelectedAllSourceNormBound rows U δ K Xmax) (hcap : 6*U^(3 : ℝ) ≤ Xmax)
    (hnorm : ∀ I ∈ S, (I.absNorm : ℝ) ≤ 6*U^w) :
    selectedNorm rows S ≤ 12*K*U^(max w ((1-δ)+δ*w)) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hUw : 1 ≤ U^w := Real.one_le_rpow hU hw.1
  have hX : 1 ≤ 6*U^w := by linarith
  have hXcap : 6*U^w ≤ Xmax := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hU hw.2) (by norm_num)).trans hcap
  have h6 : (6 : ℝ)^δ ≤ 6 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) hδ.2
  have hprod : U^(1-δ)*(6*U^w)^δ ≤ 6*U^((1-δ)+δ*w) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg hUp.le _),
      ← Real.rpow_mul hUp.le]
    calc
      _ ≤ U^(1-δ)*(6*U^(w*δ)) := by gcongr
      _ = _ := by rw [show δ*w = w*δ by ring, Real.rpow_add hUp]; ring
  have hterm1 := Real.rpow_le_rpow_of_exponent_le hU (le_max_left w ((1-δ)+δ*w))
  have hterm2 := Real.rpow_le_rpow_of_exponent_le hU (le_max_right w ((1-δ)+δ*w))
  have h := hbound.2 (6*U^w) S hX hXcap hnorm
  calc
    _ ≤ K*(6*U^w+U^(1-δ)*(6*U^w)^δ) := h
    _ ≤ K*(12*U^(max w ((1-δ)+δ*w))) := by
      apply mul_le_mul_of_nonneg_left _ hbound.1
      nlinarith
    _ = _ := by ring

theorem detector_raw_word_bound (rows : Finset O) (χ : O → Character) (base : Ideal O → ℂ)
    (hrow : ∀ z ∈ rows, ∀ I : Ideal O, idealCoeff (χ z) I = base I * idealRowHom z I)
    (hbase : ∀ I, ‖base I‖ ≤ 1) (inverse : Bool) (W : ℝ → ℂ)
    (U δ K Xmax w σ freq L : ℝ) (hU : 1 ≤ U) (hL : 0 ≤ L)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 3)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hs : Function.support W ⊆ Set.Icc (1/4 : ℝ) (9/4)) (hW : ∀ x, ‖W x‖ ≤ L)
    (hbound : SelectedAllSourceNormBound rows U δ K Xmax) (hcap : 6*U^(3 : ℝ) ≤ Xmax) :
    ∑ z ∈ rows, ‖polynomial (χ z) inverse W (U^w) σ freq‖^2 ≤
      (12*(4608*L^2))*K*U^(max w ((1-δ)+δ*w)) := by
  have hD : 1 ≤ U^w := Real.one_le_rpow hU hw.1
  have hDp : 0 < U^w := zero_lt_one.trans_le hD
  have hnorm := selectedNorm_word_bound rows (detectorSources (U^w)) U δ K Xmax w hU hδ hw
    hbound hcap (fun I hI => (mem_detectorSources.mp hI).2.trans (by nlinarith))
  have hraw := detector_raw_energy rows χ base hrow hbase inverse W (U^w) σ freq L hD hL hσ
    hs hW (detectorSources (U^w)) (detectorSources_cover W (U^w) hDp hs)
    (fun I hI => (mem_detectorSources.mp hI).1) (fun I hI => (mem_detectorSources.mp hI).2)
  exact hraw.trans ((mul_le_mul_of_nonneg_right hnorm (by positivity)).trans_eq (by ring))

theorem detector_raw_product_word_bound (rows : Finset O) (χ : O → Character)
    (base : Ideal O → ℂ)
    (hrow : ∀ z ∈ rows, ∀ I : Ideal O, idealCoeff (χ z) I = base I * idealRowHom z I)
    (hbase : ∀ I, ‖base I‖ ≤ 1) (invM invS : Bool) (WM WS : ℝ → ℂ)
    (U δ K Xmax r m σ freq L ε : ℝ) (hU : 1 ≤ U) (hL : 0 ≤ L)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hr : 0 ≤ r) (hm : 0 ≤ m) (hrm : r+m ≤ 3)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hsM : Function.support WM ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hsS : Function.support WS ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hWM : ∀ x, ‖WM x‖ ≤ L) (hWS : ∀ x, ‖WS x‖ ≤ L)
    (hbound : SelectedAllSourceNormBound rows U δ K Xmax) (hcap : 6*U^(3 : ℝ) ≤ Xmax) :
    ∑ z ∈ rows, ‖polynomial (χ z) invM WM (U^r) σ freq *
      polynomial (χ z) invS WS (U^m) σ freq‖^2 ≤
      (72*idealDivisorConstant ε hε*(4608*L^2)^2)*K*
        U^((max (r+m) ((1-δ)+δ*(r+m)))+3*ε) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hD : 1 ≤ U^r := Real.one_le_rpow hU hr
  have hN : 1 ≤ U^m := Real.one_le_rpow hU hm
  let SM := detectorSources (U^r)
  let SS := detectorSources (U^m)
  have hprod (I : Ideal O) (hI : I ∈ idealProductSources SM SS) :
      (I.absNorm : ℝ) ≤ 6*U^(r+m) := by
    rw [Real.rpow_add hUp]
    exact detectorSources_product_norm (by positivity) (by positivity) hI
  have hnorm := selectedNorm_word_bound rows (idealProductSources SM SS) U δ K Xmax (r+m)
    hU hδ ⟨by linarith, hrm⟩ hbound hcap hprod
  have hraw := detector_raw_product_energy rows χ base hrow hbase invM invS WM WS
    (U^r) (U^m) σ freq L L ε (6*U^(r+m)) hD hN hL hL hε (by positivity) hσ
    hsM hsS hWM hWS SM SS
    (detectorSources_cover WM _ (by positivity) hsM) (detectorSources_cover WS _ (by positivity) hsS)
    (fun I hI => (mem_detectorSources.mp hI).1) (fun I hI => (mem_detectorSources.mp hI).1)
    (fun I hI => (mem_detectorSources.mp hI).2) (fun I hI => (mem_detectorSources.mp hI).2)
    (fun I hI => detectorSources_product_nonzero hI) hprod
  have h6 : (6 : ℝ)^ε ≤ 6 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) hε1
  have hp : (6*U^(r+m))^ε ≤ 6*U^(3*ε) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity), ← Real.rpow_mul hUp.le]
    exact mul_le_mul h6
      (Real.rpow_le_rpow_of_exponent_le hU (mul_le_mul_of_nonneg_right hrm hε.le))
      (by positivity) (by norm_num)
  have hdiv : 0 ≤ idealDivisorConstant ε hε := (idealDivisorConstant_pos ε hε).le
  calc
    _ ≤ selectedNorm rows (idealProductSources SM SS) *
        (idealDivisorConstant ε hε * (6*U^(r+m))^ε * (4608*L^2) * (4608*L^2)) := hraw
    _ ≤ (12*K*U^(max (r+m) ((1-δ)+δ*(r+m)))) *
        (idealDivisorConstant ε hε * (6*U^(3*ε)) * (4608*L^2) * (4608*L^2)) := by
      apply mul_le_mul hnorm
      · gcongr
      · positivity
      · exact mul_nonneg (mul_nonneg (by norm_num) hbound.1) (by positivity)
    _ = _ := by rw [Real.rpow_add hUp]; ring

def detectorRawConstant (L ε : ℝ) (hε : 0 < ε) : ℝ :=
  12*(4608*L^2)+72*idealDivisorConstant ε hε*(4608*L^2)^2

theorem detectorRawConstant_nonneg (L ε : ℝ) (hε : 0 < ε) :
    0 ≤ detectorRawConstant L ε hε := by
  have := (idealDivisorConstant_pos ε hε).le
  unfold detectorRawConstant
  positivity

/-- The unit source column already counts the full selected set. This is the
SC complement; it needs neither a zero condition nor detector witnesses. -/
theorem selectedNorm_unit_card (E : Finset O) : (E.card : ℝ) ≤ selectedNorm E {1} := by
  have hone (z : O) : ordinaryPolynomial ({1} : Finset (Ideal O)) (fun _ => (1 : ℂ)) z = 1 := by
    unfold ordinaryPolynomial
    rw [Finset.sum_coe_sort ({1} : Finset (Ideal O)) (fun I => (1 : ℂ)*idealRowHom z I)]
    rw [Finset.sum_singleton, one_mul, map_one]
  have h := ordinaryPolynomial_energy E ({1} : Finset (Ideal O)) (fun _ => (1 : ℂ))
  simpa only [hone, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, Finset.card_singleton, nsmul_eq_mul, mul_one, Nat.cast_one] using h

/-- SC count on the entire selected set, valid also for the complementary
amplitude range `δ ≥ ν`. The only input is the same all-source norm. -/
theorem selected_set_SC_count (E : Finset O) (U δ K Xmax : ℝ)
    (hU : 1 ≤ U) (hδ : δ ≤ 1) (hXmax : 1 ≤ Xmax)
    (hbound : SelectedAllSourceNormBound E U δ K Xmax) :
    (E.card : ℝ) ≤ 2*K*U^(1-δ) := by
  have hnorm := hbound.2 1 ({1} : Finset (Ideal O)) (by norm_num) hXmax
    (by intro I hI; obtain rfl := Finset.mem_singleton.mp hI; norm_num)
  have hp : 1 ≤ U^(1-δ) := Real.one_le_rpow hU (by linarith)
  calc
    _ ≤ selectedNorm E {1} := selectedNorm_unit_card E
    _ ≤ K*(1+U^(1-δ)) := by simpa only [Real.one_rpow, mul_one] using hnorm
    _ ≤ _ := by nlinarith [hbound.1]

/-- The complementary SC count pays the literal HIGH energy when `δ ≥ ν`.
The actual slot-width cap is explicit. This closes the slope complement to
the three-word branch; no count beyond the norm's unit column is required. -/
theorem SC_energy_le_refined_g {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) (hδ : ν ≤ δ)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) (hscap : s ≤ M/10) :
    (1-δ)*M+ν*P+δ*s ≤ M+FrontierRefinedPrice.g ν P s M := by
  have hden : 3*(1-ν) ≠ 0 := by nlinarith [hν.2]
  have he : jointCountExponent ν ν = 1-ν := by
    change 3*(1-ν)*(1-ν)/(3*(1-ν)+2*(ν-ν)) = 1-ν
    rw [sub_self, mul_zero, add_zero]
    apply (div_eq_iff hden).2
    ring
  have hk := FrontierRefinedPrice.k_le_nu hν
  have hbase := FrontierRefinedPrice.joint_energy_le_g hν
    (show ν ∈ Set.Icc (500000001/1000000000 : ℝ) ν from ⟨by linarith [hν.1], le_rfl⟩) hM hs0 (P := P)
  rw [he, min_eq_right (by linarith)] at hbase
  have hdiff := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hδ)
    (show s-M ≤ 0 by linarith)
  nlinarith

private theorem raise_raw_bound {F C C' K U b ε : ℝ}
    (h : F ≤ C*K*U^b) (hC : 0 ≤ C) (hCC : C ≤ C') (hK : 0 ≤ K)
    (hU : 1 ≤ U) (hε : 0 ≤ ε) : F ≤ C'*K*U^(b+3*ε) := by
  have hpow := Real.rpow_le_rpow_of_exponent_le hU (show b ≤ b+3*ε by linarith)
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right hCC hK) hpow (by positivity)
    (mul_nonneg (hC.trans hCC) hK))

private theorem subtype_partial_sum_le (E : Finset O) (rows : Finset E)
    (f : O → ℝ) (hpos : ∀ u, 0 ≤ f u) :
    ∑ u ∈ rows, f u.val ≤ ∑ u ∈ E, f u := by
  rw [← Finset.sum_coe_sort E f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _ => hpos u.val)

/-- The word geometry uses only `1/2 ≤ δ ≤ ν ≤ 3/4`; the former `.65`
wrapper floor is unnecessary. This includes the `.58` density floor and
its buffered children. -/
theorem count_word_min_le {ν δ r m : ℝ} (_hδ : (1/2 : ℝ) ≤ δ)
    (hδν : δ ≤ ν) (hν : ν ≤ 3/4)
    (hr : r ≤ 1) (hm : m ≤ 1/2) (hrm : 1 ≤ r+m) :
    min (wordEnvelope ν δ r) (min (wordEnvelope ν δ (2*m)) (wordEnvelope ν δ (r+m))) ≤
      jointCountExponent ν δ := by
  have hd : 0 < witnessDen ν δ := by unfold witnessDen; linarith
  have hL : lStar ν δ ≤ 1 := by
    unfold lStar mStar
    rw [← mul_div_assoc, div_le_iff₀ hd]
    unfold witnessDen
    linarith
  have hH : 1 ≤ hStar ν δ := by
    unfold hStar mStar
    rw [← mul_div_assoc, le_div_iff₀ hd]
    unfold witnessDen
    linarith
  have he : jointCountExponent ν δ = (1-δ)-(ν-δ)*lStar ν δ := by
    unfold jointCountExponent lStar mStar
    field_simp
    unfold witnessDen
    ring
  have hword (w : ℝ) (hw : w ∈ Set.Icc (lStar ν δ) (hStar ν δ)) :
      wordEnvelope ν δ w ≤ jointCountExponent ν δ := by
    unfold wordEnvelope
    apply max_le
    · rw [jointCountExponent_upper_identity]
      exact mul_le_mul_of_nonneg_left hw.2 (by linarith)
    · rw [he]
      have h := mul_le_mul_of_nonneg_left hw.1 (sub_nonneg.mpr hδν)
      linarith
  by_cases hrL : lStar ν δ ≤ r
  · exact (min_le_left _ _).trans (hword r ⟨hrL, hr.trans hH⟩)
  · by_cases hmL : lStar ν δ ≤ 2*m
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        (hword (2*m) ⟨hmL, by linarith⟩)
    · apply ((min_le_right _ _).trans (min_le_right _ _)).trans
      apply hword (r+m)
      refine ⟨hL.trans hrm, ?_⟩
      have hr' : r < 2*mStar ν δ := lt_of_not_ge hrL
      have hm' : 2*m < 2*mStar ν δ := lt_of_not_ge hmL
      unfold hStar
      linarith

theorem count_word_length_error {ν δ w v L : ℝ}
    (hδ : (1/2 : ℝ) ≤ δ) (hδν : δ ≤ ν) (hν : ν ≤ 3/4) (hL : |w-v| ≤ L) :
    wordEnvelope ν δ w ≤ wordEnvelope ν δ v+(1/2)*L := by
  have hlo := (abs_le.mp hL).1
  have hhi := (abs_le.mp hL).2
  have hLp : 0 ≤ L := (abs_nonneg _).trans hL
  have hb : 0 ≤ 1-ν := by linarith
  have ha : 0 ≤ ν-δ := by linarith
  have hb' : 1-ν ≤ 1/2 := by linarith
  have ha' : ν-δ ≤ 1/2 := by linarith
  have h1 := mul_le_mul_of_nonneg_left hhi hb
  have h2 := mul_le_mul_of_nonneg_right hb' hLp
  have h3 := mul_le_mul_of_nonneg_left hlo ha
  have h4 := mul_le_mul_of_nonneg_right ha' hLp
  have hm1 := le_max_left ((1-ν)*v) ((1-δ)-(ν-δ)*v)
  have hm2 := le_max_right ((1-ν)*v) ((1-δ)-(ν-δ)*v)
  unfold wordEnvelope
  exact max_le (by nlinarith) (by nlinarith)

theorem count_buffered_word_min_le {ν δ r m ε : ℝ}
    (hδ : (1/2 : ℝ) ≤ δ) (hδν : δ ≤ ν) (hν : ν ≤ 3/4) (hε : 0 ≤ ε)
    (hm0 : 0 ≤ m) (hr : r ≤ 1+ε) (hm : m ≤ 1/2+75*ε) (hrm : 1-ε ≤ r+m) :
    min (wordEnvelope ν δ r) (min (wordEnvelope ν δ (2*m)) (wordEnvelope ν δ (r+m))) ≤
      jointCountExponent ν δ+76*ε := by
  let m' := min m (1/2)
  let r' := max (min r 1) (1-m')
  have hm'0 : 0 ≤ m' := le_min hm0 (by norm_num)
  have hm'1 : m' ≤ 1/2 := min_le_right _ _
  have hm'm : m' ≤ m := min_le_left _ _
  have hmm' : m-75*ε ≤ m' := le_min (by linarith) (by linarith)
  have hr'1 : r' ≤ 1 := max_le (min_le_right _ _) (by linarith)
  have hr'm' : 1 ≤ r'+m' := by linarith [le_max_right (min r 1) (1-m')]
  have hrr' : r-ε ≤ r' := (le_min (by linarith) (by linarith)).trans (le_max_left _ _)
  have hr'r : r' ≤ r+76*ε := max_le ((min_le_left _ _).trans (by linarith)) (by linarith)
  have hmr : |m-m'| ≤ 75*ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrr : |r-r'| ≤ 76*ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have htwo : |2*m-2*m'| ≤ 150*ε := abs_le.mpr
    ⟨by linarith [(abs_le.mp hmr).1], by linarith [(abs_le.mp hmr).2]⟩
  have hsum : |(r+m)-(r'+m')| ≤ 151*ε := abs_le.mpr
    ⟨by linarith [(abs_le.mp hrr).1, (abs_le.mp hmr).1],
      by linarith [(abs_le.mp hrr).2, (abs_le.mp hmr).2]⟩
  have h1 := count_word_length_error hδ hδν hν hrr
  have h2 := count_word_length_error hδ hδν hν htwo
  have h3 := count_word_length_error hδ hδν hν hsum
  have hg := count_word_min_le hδ hδν hν hr'1 hm'1 hr'm'
  have he1 : wordEnvelope ν δ r ≤ wordEnvelope ν δ r'+76*ε := by linarith
  have he2 : wordEnvelope ν δ (2*m) ≤ wordEnvelope ν δ (2*m')+76*ε := by linarith
  have he3 : wordEnvelope ν δ (r+m) ≤ wordEnvelope ν δ (r'+m')+76*ε := by linarith
  have h := min_le_min he1 (min_le_min he2 he3)
  simp only [min_add_add_right] at h
  linarith

/-- One entire supported-witness fiber, with all three raw moments derived
from the stated operator norm. No energy or count assertion is assumed. -/
theorem supported_witness_fiber_count {Label : Type*}
    (E : Finset O) (rows : Finset E) (χ : O → Label → Character)
    (base : Label → Ideal O → ℂ)
    (hrow : ∀ z ∈ E, ∀ j I, idealCoeff (χ z j) I = base j I * idealRowHom z I)
    (hbase : ∀ j I, ‖base j I‖ ≤ 1)
    (U a δ K Xmax ε T allowance height L : ℝ) (i : ℕ)
    (hU : 1 < U) (hν : 2*a-1 ∈ Set.Icc (1/2 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (1/2 : ℝ) (2*a-1)) (hε : 0 < ε) (hεsmall : ε ≤ 1/1000)
    (hbound : SelectedAllSourceNormBound E U δ K Xmax) (hcap : 6*U^(3 : ℝ) ≤ Xmax)
    (w : ∀ u : E, SupportedWitness (χ u.val) U a ε 1 T allowance i)
    (label : Label) (J Kdy : Fin (dyadicLength U))
    (hlabel : ∀ u ∈ rows, (w u).label = label)
    (hJ : ∀ u ∈ rows, (w u).left = J) (hK : ∀ u ∈ rows, (w u).right = Kdy)
    (hh : 0 ≤ height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height)
    (hL : 1 ≤ L)
    (hplain : ∀ n : ℕ, n ≤ 2 → Function.support ((logProfile^[n]) positiveAnnular) ⊆
      Set.Icc (1/4 : ℝ) (9/4) ∧ ∀ x, ‖(logProfile^[n]) positiveAnnular x‖ ≤ L)
    (hinverse : ∀ (n : ℕ) (Dstar D : ℝ), n ≤ 2 →
      Function.support ((logProfile^[n]) (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)) ⊆
        Set.Icc (1/4 : ℝ) (9/4) ∧
      ∀ x, ‖(logProfile^[n]) (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) x‖ ≤ L) :
    (rows.card : ℝ) ≤ 192*(1+height)*detectorRawConstant L ε hε*K*
      U^(jointCountExponent (2*a-1) δ+83*ε) := by
  by_cases hne : rows.Nonempty
  · let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^Kdy.val)
    let WM := HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^(1 : ℝ)) (U^r)
    let W : ∀ u : E, Witness (χ u.val) U a ε 1 T allowance i := fun u => (w u).toWitness
    let C := detectorRawConstant L ε hε
    let CM := 192*(1+height)*C*K
    have hUp : 0 < U := zero_lt_one.trans hU
    have hr0 : 0 ≤ r := Real.logb_nonneg hU (one_le_pow₀ (by norm_num))
    have hm0 : 0 ≤ m := Real.logb_nonneg hU (one_le_pow₀ (by norm_num))
    have hl := fiber_lengths rows hne (fun u : E => χ u.val) U a ε 1 T allowance i hU w J Kdy hJ hK
    change 1-r-ε ≤ m ∧ r ≤ 1+ε ∧ m ≤ 1/2+75*ε ∧ 1-1/2-76*ε ≤ r ∧ 0 ≤ m at hl
    have hr3 : r ≤ 3 := by linarith [hl.2.1]
    have hm3 : 2*m ≤ 3 := by linarith [hl.2.2.1]
    have hrm3 : r+m ≤ 3 := by linarith [hl.2.1, hl.2.2.1]
    have hδ01 : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hδ.1], by linarith [hδ.2, hν.2]⟩
    have ha : 0 ≤ a := by linarith [hν.1]
    have hCp : 0 ≤ C := detectorRawConstant_nonneg L ε hε
    have hK0 : 0 ≤ K := hbound.1
    have hC1 : 12*(4608*L^2) ≤ C := by
      have := (idealDivisorConstant_pos ε hε).le
      dsimp [C, detectorRawConstant]
      exact le_add_of_nonneg_right (by positivity)
    have hC2 : 72*idealDivisorConstant ε hε*(4608*L^2)^2 ≤ C := by
      dsimp [C, detectorRawConstant]
      nlinarith [sq_nonneg L]
    have hrawM (n : ℕ) (hn : n ≤ 2) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (t : ℝ) (_ht : t ∈ Set.Icc (-height) height) :
        ∑ u ∈ rows, ‖polynomial (χ u.val label) true ((logProfile^[n]) WM) (U^r) s t * 1‖^2 ≤
          C*K*U^((max r ((1-δ)+δ*r))+3*ε) := by
      simp only [mul_one]
      apply (subtype_partial_sum_le E rows
        (fun z => ‖polynomial (χ z label) true ((logProfile^[n]) WM) (U^r) s t‖^2)
        (fun _ => sq_nonneg _)).trans
      exact raise_raw_bound (detector_raw_word_bound E (fun z => χ z label) (base label)
        (fun z hz I => hrow z hz label I) (hbase label) true ((logProfile^[n]) WM)
        U δ K Xmax r s t L hU.le (by linarith) hδ01 ⟨hr0, hr3⟩ hs
        (hinverse n _ _ hn).1 (hinverse n _ _ hn).2 hbound hcap)
        (by positivity) hC1 hbound.1 hU.le hε.le
    have hrawP (j k : ℕ) (hjk : j+k ≤ 2) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (t : ℝ) (_ht : t ∈ Set.Icc (-height) height) :
        ∑ u ∈ rows, ‖polynomial (χ u.val label) false ((logProfile^[j]) positiveAnnular) (U^m) s t *
          polynomial (χ u.val label) false ((logProfile^[k]) positiveAnnular) (U^m) s t * 1‖^2 ≤
          C*K*U^((max (2*m) ((1-δ)+δ*(2*m)))+3*ε) := by
      simp only [mul_one]
      apply (subtype_partial_sum_le E rows (fun z =>
        ‖polynomial (χ z label) false ((logProfile^[j]) positiveAnnular) (U^m) s t *
          polynomial (χ z label) false ((logProfile^[k]) positiveAnnular) (U^m) s t‖^2)
        (fun _ => sq_nonneg _)).trans
      have h := detector_raw_product_word_bound E (fun z => χ z label) (base label)
        (fun z hz I => hrow z hz label I) (hbase label) false false _ _
        U δ K Xmax m m s t L ε hU.le (by linarith) hδ01 hm0 hm0 (by linarith)
        hε (by linarith) hs (hplain j (by omega)).1 (hplain k (by omega)).1
        (hplain j (by omega)).2 (hplain k (by omega)).2 hbound hcap
      have h' : _ ≤ C*K*U^((max (m+m) ((1-δ)+δ*(m+m)))+3*ε) :=
        h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hbound.1) (by positivity))
      simpa only [two_mul] using h'
    have hrawMS (j k : ℕ) (hjk : j+k ≤ 2) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (t : ℝ) (_ht : t ∈ Set.Icc (-height) height) :
        ∑ u ∈ rows, ‖polynomial (χ u.val label) true ((logProfile^[j]) WM) (U^r) s t *
          polynomial (χ u.val label) false ((logProfile^[k]) positiveAnnular) (U^m) s t * 1‖^2 ≤
          C*K*U^((max (r+m) ((1-δ)+δ*(r+m)))+3*ε) := by
      simp only [mul_one]
      apply (subtype_partial_sum_le E rows (fun z =>
        ‖polynomial (χ z label) true ((logProfile^[j]) WM) (U^r) s t *
          polynomial (χ z label) false ((logProfile^[k]) positiveAnnular) (U^m) s t‖^2)
        (fun _ => sq_nonneg _)).trans
      exact (detector_raw_product_word_bound E (fun z => χ z label) (base label)
        (fun z hz I => hrow z hz label I) (hbase label) true false _ _
        U δ K Xmax r m s t L ε hU.le (by linarith) hδ01 hr0 hm0 hrm3
        hε (by linarith) hs (hinverse j _ _ (by omega)).1 (hplain k (by omega)).1
        (hinverse j _ _ (by omega)).2 (hplain k (by omega)).2 hbound hcap).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hbound.1) (by positivity))
    have hM := HeckeDetectorFiberEnergy.inverse_energy rows (fun u : E => χ u.val)
      U a ε 1 T allowance i ha W label WM (U^r) (1/4) (9/4)
      (C*K*U^((max r ((1-δ)+δ*r))+3*ε)) (fun _ => 1) (by positivity) (by norm_num)
      (hinverse 0 _ _ (by omega)).1 (by positivity) height hh hfreq hrawM
    have hP := HeckeDetectorFiberEnergy.plain_energy rows (fun u : E => χ u.val)
      U a ε 1 T allowance i ha W label positiveAnnular (U^m) (1/4) (9/4)
      (C*K*U^((max (2*m) ((1-δ)+δ*(2*m)))+3*ε)) (fun _ => 1) (by positivity) (by norm_num)
      positiveAnnular_support (by positivity) height hh hfreq hrawP
    have hMS := detector_mixed_witness_energy rows (fun u : E => χ u.val)
      U a ε 1 T allowance i ha W label WM positiveAnnular (U^r) (U^m) (by positivity) (by positivity)
      (detectorSources (U^r)) (detectorSources (U^m))
      (detectorSources_cover WM _ (by positivity) (hinverse 0 _ _ (by omega)).1)
      (detectorSources_cover positiveAnnular _ (by positivity) positiveAnnular_support)
      (fun _ => 1) (C*K*U^((max (r+m) ((1-δ)+δ*(r+m)))+3*ε)) height
      (by positivity) hh hfreq hrawMS
    have hMe : (∑ u ∈ rows, ‖polynomial (χ u.val label) true WM (U^r) (w u).zero.re (w u).frequency‖^2) ≤
        CM*U^((max r ((1-δ)+δ*r))+3*ε) := by
      simp only [mul_one] at hM
      have hp := Real.rpow_nonneg hUp.le ((max r ((1-δ)+δ*r))+3*ε)
      refine hM.trans ?_
      calc
        _ ≤ 192*(1+height)*(C*K*U^((max r ((1-δ)+δ*r))+3*ε)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by dsimp [CM]; ring
    have hPe : (∑ u ∈ rows, ‖polynomial (χ u.val label) false positiveAnnular
        (U^m) (w u).zero.re (w u).frequency ^ 2‖^2) ≤
        CM*U^((max (2*m) ((1-δ)+δ*(2*m)))+3*ε) := by
      simpa only [mul_one, ← pow_two, CM, mul_assoc] using hP
    have hMSe : (∑ u ∈ rows, ‖polynomial (χ u.val label) true WM (U^r) (w u).zero.re (w u).frequency *
        polynomial (χ u.val label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2) ≤
        CM*U^((max (r+m) ((1-δ)+δ*(r+m)))+3*ε) := by
      simpa only [mul_one, CM, mul_assoc] using hMS
    have hc := actual_three_word_fiber_count rows (fun u : E => χ u.val) U a ε 1 T allowance i hU W
      label J Kdy hlabel hJ hK CM CM CM
      ((max r ((1-δ)+δ*r))+3*ε) ((max (2*m) ((1-δ)+δ*(2*m)))+3*ε)
      ((max (r+m) ((1-δ)+δ*(r+m)))+3*ε) hMe hPe hMSe
    have hexp (x : ℝ) : max x ((1-δ)+δ*x)-(2*a-1)*x = wordEnvelope (2*a-1) δ x := by
      rw [← max_sub_sub_right]
      unfold wordEnvelope
      congr 1 <;> ring
    have hsmall := count_buffered_word_min_le hδ.1 hδ.2 hν.2 hε.le hm0 hl.2.1 hl.2.2.1 (by linarith [hl.1])
    have hCM : 0 ≤ CM := by dsimp [CM]; positivity
    have hword (x : ℝ) (hx : wordEnvelope (2*a-1) δ x ≤ jointCountExponent (2*a-1) δ+76*ε) :
        CM*U^((max x ((1-δ)+δ*x)+3*ε)-((2*a-1)*x-4*ε)) ≤
          CM*U^(jointCountExponent (2*a-1) δ+83*ε) := by
      apply mul_le_mul_of_nonneg_left _ hCM
      apply Real.rpow_le_rpow_of_exponent_le hU.le
      rw [show max x ((1-δ)+δ*x)+3*ε-((2*a-1)*x-4*ε) =
        (max x ((1-δ)+δ*x)-(2*a-1)*x)+7*ε by ring, hexp]
      linarith
    change (rows.card : ℝ) ≤ CM*U^(jointCountExponent (2*a-1) δ+83*ε)
    rcases min_le_iff.mp hsmall with h | h
    · apply (hc.trans (min_le_left _ _)).trans
      exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le
        (show max r ((1-δ)+δ*r)+3*ε-((2*a-1)*r-2*ε) ≤
          max r ((1-δ)+δ*r)+3*ε-((2*a-1)*r-4*ε) by linarith)) hCM).trans (hword r h)
    · rcases min_le_iff.mp h with h | h
      · exact ((hc.trans (min_le_right _ _)).trans (min_le_left _ _)).trans (hword (2*m) h)
      · exact ((hc.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (hword (r+m) h)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have := detectorRawConstant_nonneg L ε hε
    have := hbound.1
    positivity

/-- Uniform whole-core count. The sole analytic operator input is the
displayed all-source norm, with one constant `K` for the actual selected set.
All actual dictionary and dyadic fibers are summed. The constant is chosen
before the fixed finite dictionary, all row sets, slopes, scales and heights.
-/
theorem uniform_supported_core_count (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/1000) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Label : Type*} [Fintype Label] (E : Finset O) (χ : O → Label → Character)
      (base : Label → Ideal O → ℂ),
    (∀ z ∈ E, ∀ j I, idealCoeff (χ z j) I = base j I * idealRowHom z I) →
    (∀ j I, ‖base j I‖ ≤ 1) →
    ∀ (U a δ K Xmax T allowance height : ℝ) (i : ℕ),
    1 < U → 2*a-1 ∈ Set.Icc (1/2 : ℝ) (3/4) →
    δ ∈ Set.Icc (1/2 : ℝ) (2*a-1) →
    SelectedAllSourceNormBound E U δ K Xmax → 6*U^(3 : ℝ) ≤ Xmax →
    (∀ u : E, SupportedWitness (χ u.val) U a ε 1 T allowance i) →
    0 ≤ height → 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    (E.card : ℝ) ≤ C*(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*
      (1+height)*K*U^(jointCountExponent (2*a-1) δ+83*ε) := by
  obtain ⟨L, hL, hplain, hinverse⟩ := exists_actual_detector_profile_bound
  have hdiv := idealDivisorConstant_pos ε hε
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hC : 0 < 192*detectorRawConstant L ε hε := by
    unfold detectorRawConstant
    positivity
  refine ⟨192*detectorRawConstant L ε hε, hC, ?_⟩
  intro Label _ E χ base hrow hbase U a δ K Xmax T allowance height i hU hν hδ hbound hcap w hh hfreq
  let W : ∀ u : E, Witness (χ u.val) U a ε 1 T allowance i := fun u => (w u).toWitness
  let fiber (j : Label) (J Kdy : Fin (dyadicLength U)) :=
    HeckeDetectorDynamicSelection.fiber (Finset.univ : Finset E) (fun u : E => χ u.val)
      U a ε 1 T allowance i W j J Kdy
  have hcard : (E.card : ℝ) = ∑ j : Label, ∑ J : Fin (dyadicLength U),
      ∑ Kdy : Fin (dyadicLength U), ((fiber j J Kdy).card : ℝ) := by
    have h := HeckeDetectorDynamicSelection.card_eq_sum_fibers (Finset.univ : Finset E)
      (fun u : E => χ u.val) U a ε 1 T allowance i W
    simpa only [Finset.card_univ, Fintype.card_coe, Nat.cast_sum, fiber] using congrArg (Nat.cast : ℕ → ℝ) h
  rw [hcard]
  calc
    _ ≤ ∑ _j : Label, ∑ _J : Fin (dyadicLength U), ∑ _Kdy : Fin (dyadicLength U),
        192*(1+height)*detectorRawConstant L ε hε*K*U^(jointCountExponent (2*a-1) δ+83*ε) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro J hJ
      apply Finset.sum_le_sum
      intro Kdy hK
      apply supported_witness_fiber_count E (fiber j J Kdy) χ base hrow hbase
        U a δ K Xmax ε T allowance height L i hU hν hδ hε hεsmall hbound hcap w j J Kdy
      · intro u hu
        exact (Finset.mem_filter.mp hu).2.1
      · intro u hu
        exact (Finset.mem_filter.mp hu).2.2.1
      · intro u hu
        exact (Finset.mem_filter.mp hu).2.2.2
      · exact hh
      · exact hfreq
      · exact hL
      · exact hplain
      · exact hinverse
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Lowering only the requested zero slope preserves the actual detector,
zero, labels, and long-tail length. Nonnegative dyadic lengths pay the weaker
response directly; no fresh witness selection is made. -/
def lowerWitnessSlope {Label : Type*} {χ : Label → Character}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1 < U)
    (a₀ : ℝ) (ha₀ : a₀ ≤ a) : Witness χ U a₀ ε tstar T allowance i := by
  have hr0 : 0 ≤ w.r := by
    rw [w.left_exponent hU]
    exact Real.logb_nonneg hU (one_le_pow₀ (by norm_num))
  have hm0 : 0 ≤ w.m := w.plain_length_lower
  exact {
    label := w.label, zero := w.zero, zero_eq := w.zero_eq,
    zero_lower := ha₀.trans w.zero_lower, zero_height := w.zero_height,
    left := w.left, right := w.right, nu := w.nu, r := w.r, m := w.m,
    nu_bound := w.nu_bound, left_scale := w.left_scale, right_scale := w.right_scale,
    inverse_length_lower := w.inverse_length_lower,
    inverse_length_upper := w.inverse_length_upper,
    plain_length_lower := w.plain_length_lower, plain_length_upper := w.plain_length_upper,
    inverse_spike := (Real.rpow_le_rpow_of_exponent_le hU.le
      (show (2*a₀-1)*w.r-2*ε ≤ (2*a-1)*w.r-2*ε by nlinarith)).trans w.inverse_spike,
    plain_spike := (Real.rpow_le_rpow_of_exponent_le hU.le
      (show (2*a₀-1)*w.m-2*ε ≤ (2*a-1)*w.m-2*ε by nlinarith)).trans w.plain_spike }

def lowerSupportedWitnessSlope {Label : Type*} {χ : Label → Character}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε tstar T allowance i) (hU : 1 < U)
    (a₀ : ℝ) (ha₀ : a₀ ≤ a) : SupportedWitness χ U a₀ ε tstar T allowance i where
  toWitness := lowerWitnessSlope w.toWitness hU a₀ ha₀
  product_length_lower := w.product_length_lower

/-- Actual buffered zero count for a fixed finite free-core dictionary,
relative only to the explicit all-source norm. The supported witnesses,
including the genuine long tail, are constructed from the accepted OAI
zero detector. No witness, energy, or count assertion is an input.

The free character conductor bound is `Z^d`; a moving root mask has not been
inserted into that conductor. The constant and eventual threshold are fixed
before the dictionary, selected set, live height, or slot coefficients.
-/
theorem buffered_core_zero_count (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*η)
    (hε : 0 < ε) (hεsmall : ε ≤ 1/1000) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η ≤ ε/2) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    1 < Z^d →
    ∀ {Label : Type*} [Fintype Label] (E : Finset O) (χ : O → Label → Character)
      (hχ : ∀ u : E, ∀ j, (χ u.val j).residue ≠ 1)
      (base : Label → Ideal O → ℂ),
    (∀ z ∈ E, ∀ j J, idealCoeff (χ z j) J = base j J * idealRowHom z J) →
    (∀ j J, ‖base j J‖ ≤ 1) →
    ∀ (a a₀ δ K Xmax height : ℝ) (i : ℕ), i ≤ I → a₀ ≤ a → a ≤ 1 →
    2*a₀-1 ∈ Set.Icc (1/2 : ℝ) (3/4) → δ ∈ Set.Icc (1/2 : ℝ) (2*a₀-1) →
    (∀ u : E, HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u)
      (3*(i+1 : ℕ)*Z^τ) < a+2*e) →
    (∀ u : E, a ≤ HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) ((3*i : ℕ)*Z^τ)) →
    (∀ u : E, ∀ j, (χ u.val j).modulus.absNorm ≤ Z^d) →
    SelectedAllSourceNormBound E (Z^d) δ K Xmax → 6*(Z^d)^(3 : ℝ) ≤ Xmax →
    0 ≤ height → 2*Real.pi*(Z^d)^(τ/(2*dmax))+(3*i : ℕ)*Z^τ ≤ height →
    (E.card : ℝ) ≤ C*(Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*
      (1+height)*K*(Z^d)^(jointCountExponent (2*a₀-1) δ+83*ε) := by
  obtain ⟨C, hC, hcount⟩ := uniform_supported_core_count ε hε hεsmall
  obtain ⟨Z₀, hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨C, Z₀, hC, ?_⟩
  intro Z hZ d hd hd' hU Label _ E χ hχ base hrow hbase a a₀ δ K Xmax height i hi haa₀ ha hν hδ
    hnext hcurrent hconductor hbound hcap hh hfreq
  obtain ⟨w⟩ := hZ₀ Z hZ d hd hd' (fun u : E => χ u.val) hχ a i hi
    (by linarith [hν.1]) ha hnext hcurrent hconductor
    1 (by norm_num) (by norm_num)
  exact hcount E χ base hrow hbase (Z^d) a₀ δ K Xmax (Z^τ) ((Z^d)^(τ/(2*dmax))) height i
    hU hν hδ hbound hcap (fun u => lowerSupportedWitnessSlope (w u) hU a₀ haa₀) hh hfreq

def detectorZeroBinCount (e : ℝ) : ℕ := ⌈1/e⌉₊+1

/-- Actual finite buffered-bin selection above a demanded zero slope. The
explicit `e` guard pays the gap between a zero maximum and the lower bin
endpoint; it is part of the later energy error budget. -/
theorem finite_actual_buffered_bins {Label : Type*} [Fintype Label]
    (E : Finset O) (χ : O → Label → Character)
    (hχ : ∀ u : E, ∀ j, (χ u.val j).residue ≠ 1)
    (T e b : ℝ) (n : ℕ) (hT : 2 < T) (he : 0 < e) (hn : 0 < n)
    (hwidth : (49/100 : ℝ) ≤ (n : ℝ)*e)
    (hzero : ∀ u : E, b+e ≤ HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) T) :
    ∃ index : E → Fin (n+1) × Fin (detectorZeroBinCount e), ∀ u : E,
      let a : ℝ := 51/100+e*(index u).2.val
      b ≤ a ∧ a ≤ 1 ∧
      a ≤ HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (3*((index u).1.val : ℕ)*T) ∧
      HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u)
        (3*((index u).1.val+1 : ℕ)*T) < a+2*e := by
  have hex (u : E) : ∃ p : Fin (n+1) × Fin (detectorZeroBinCount e),
      let a : ℝ := 51/100+e*p.2.val
      b ≤ a ∧ a ≤ 1 ∧
      a ≤ HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (3*(p.1.val : ℕ)*T) ∧
      HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (3*(p.1.val+1 : ℕ)*T) < a+2*e := by
    obtain ⟨i, k, hi, hin, ha, hcurrent, hbin, hnext, _⟩ :=
      HeckeDetectorZeros.exists_actual_buffered_bin (χ u.val) (hχ u) T e hT he n hn hwidth
    have hk : (k : ℝ) ≤ 1/e := (le_div_iff₀ he).2 (by nlinarith [ha])
    have hk' : k ≤ ⌈1/e⌉₊ := by
      exact_mod_cast hk.trans (Nat.le_ceil (1/e))
    have hk'' : k < detectorZeroBinCount e := by dsimp [detectorZeroBinCount]; omega
    have hmono := HeckeDetectorZeros.zeroMaximum_mono (χ u.val) (hχ u)
      (show T ≤ 3*(i : ℝ)*T by
        have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
        nlinarith)
    refine ⟨(⟨i, by omega⟩, ⟨k, hk''⟩), ?_, ha, hcurrent, hnext⟩
    have hmon := (hzero u).trans hmono
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (show b ≤ 51/100+e*(k : ℝ) by linarith [hbin])
  exact ⟨fun u => Classical.choose (hex u), fun u => Classical.choose_spec (hex u)⟩

theorem SelectedAllSourceNormBound.mono_rows {E F : Finset O} (hFE : F ⊆ E)
    {U δ K Xmax : ℝ} (h : SelectedAllSourceNormBound E U δ K Xmax) :
    SelectedAllSourceNormBound F U δ K Xmax := by
  refine ⟨h.1, ?_⟩
  intro X S hX hXmax hnorm
  exact (selectedNorm_mono_rows hFE S).trans (h.2 X S hX hXmax hnorm)

/-- Whole core zero count before choosing any zero bin or finite ray state.
Their finite costs are explicit. The zero guard has the `e` buffer used by
the actual OAI bin selection, and the norm constant is the same for every
selected child because it is inherited by row restriction.
-/
theorem unpartitioned_core_zero_count (dmin dmax τ ε e κ η : ℝ) (n : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*η)
    (hε : 0 < ε) (hεsmall : ε ≤ 1/1000) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η ≤ ε/2)
    (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ (n : ℝ)*e) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    1 < Z^d → 2 < Z^τ →
    ∀ {Label Ray : Type*} [Fintype Label] [Fintype Ray]
      (E : Finset O) (χ : O → Label → Character) (ray : O → Ray)
      (hχ : ∀ u : E, ∀ j, (χ u.val j).residue ≠ 1)
      (base : Ray → Label → Ideal O → ℂ),
    (∀ z ∈ E, ∀ j J, idealCoeff (χ z j) J = base (ray z) j J * idealRowHom z J) →
    (∀ r j J, ‖base r j J‖ ≤ 1) →
    ∀ (a₀ δ K Xmax height : ℝ),
    2*a₀-1 ∈ Set.Icc (1/2 : ℝ) (3/4) → δ ∈ Set.Icc (1/2 : ℝ) (2*a₀-1) →
    (∀ u : E, a₀+e ≤ HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (Z^τ)) →
    (∀ u : E, ∀ j, (χ u.val j).modulus.absNorm ≤ Z^d) →
    SelectedAllSourceNormBound E (Z^d) δ K Xmax → 6*(Z^d)^(3 : ℝ) ≤ Xmax →
    0 ≤ height → 2*Real.pi*(Z^d)^(τ/(2*dmax))+(3*n : ℕ)*Z^τ ≤ height →
    (E.card : ℝ) ≤ C*((n+1 : ℕ) : ℝ)*(detectorZeroBinCount e : ℝ)*
      (Fintype.card Ray : ℝ)*(Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*
      (1+height)*K*(Z^d)^(jointCountExponent (2*a₀-1) δ+83*ε) := by
  obtain ⟨C, Z₀, hC, hcount⟩ := buffered_core_zero_count dmin dmax τ ε e κ η n
    hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκ hκ' hη hbudget
  refine ⟨C, Z₀, hC, ?_⟩
  intro Z hZ d hd hd' hU hT Label Ray _ _ E χ ray hχ base hrow hbase
    a₀ δ K Xmax height hν hδ hzero hconductor hbound hcap hh hfreq
  by_cases hne : E.Nonempty
  · obtain ⟨index, hindex⟩ := finite_actual_buffered_bins E χ hχ (Z^τ) e a₀ n hT he hn hwidth hzero
    obtain ⟨z₀, hz₀⟩ := hne
    let f : O → (Fin (n+1) × Fin (detectorZeroBinCount e)) × Ray := fun z =>
      if hz : z ∈ E then (index ⟨z, hz⟩, ray z) else (index ⟨z₀, hz₀⟩, ray z₀)
    let child (p : (Fin (n+1) × Fin (detectorZeroBinCount e)) × Ray) := E.filter (fun z => f z = p)
    have hchild (p : (Fin (n+1) × Fin (detectorZeroBinCount e)) × Ray) :
        ((child p).card : ℝ) ≤ C*(Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*
          (1+height)*K*(Z^d)^(jointCountExponent (2*a₀-1) δ+83*ε) := by
      have hsub : child p ⊆ E := Finset.filter_subset _ _
      have hdata (u : child p) :
          a₀ ≤ 51/100+e*p.1.2.val ∧ 51/100+e*p.1.2.val ≤ 1 ∧
          51/100+e*p.1.2.val ≤ HeckeDetectorZeros.zeroMaximum (χ u.val)
            (hχ ⟨u.val, hsub u.property⟩) (3*(p.1.1.val : ℕ)*Z^τ) ∧
          HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ ⟨u.val, hsub u.property⟩)
            (3*(p.1.1.val+1 : ℕ)*Z^τ) < 51/100+e*p.1.2.val+2*e := by
        have hf := (Finset.mem_filter.mp u.property).2
        have hf' : index ⟨u.val, hsub u.property⟩ = p.1 := by
          simpa only [f, dite_eq_left (hsub u.property)] using congrArg Prod.fst hf
        have h := hindex ⟨u.val, hsub u.property⟩
        rw [hf'] at h
        exact h
      by_cases hcp : (child p).Nonempty
      · obtain ⟨u, hu⟩ := hcp
        have ha := hdata ⟨u, hu⟩
        refine hcount Z hZ d hd hd' hU (child p) χ
          (fun u => hχ ⟨u.val, hsub u.property⟩) (base p.2) ?_ (hbase p.2)
          (51/100+e*p.1.2.val) a₀ δ K Xmax height p.1.1.val
          (Nat.le_of_lt_succ p.1.1.isLt) ha.1 ha.2.1 hν hδ ?_ ?_ ?_
          (SelectedAllSourceNormBound.mono_rows hsub hbound) hcap hh ?_
        · intro z hz j J
          have hray : ray z = p.2 := by
            have hf := (Finset.mem_filter.mp hz).2
            simpa only [f, dite_eq_left (hsub hz)] using congrArg Prod.snd hf
          simpa only [hray] using hrow z (hsub hz) j J
        · intro u
          exact (hdata u).2.2.2
        · intro u
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hdata u).2.2.1
        · intro u j
          exact hconductor ⟨u.val, hsub u.property⟩ j
        · have hi : ((3*p.1.1.val : ℕ) : ℝ) ≤ ((3*n : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ p.1.1.isLt)
          exact (add_le_add_right (mul_le_mul_of_nonneg_right hi (by positivity)) _).trans hfreq
      · rw [Finset.not_nonempty_iff_eq_empty.mp hcp]
        simp only [Finset.card_empty, Nat.cast_zero]
        have := hbound.1
        positivity
    have hcard : (E.card : ℝ) = ∑ p : (Fin (n+1) × Fin (detectorZeroBinCount e)) × Ray,
        ((child p).card : ℝ) := by
      have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ) (f := f)
        (fun _ _ => Finset.mem_univ _)
      exact_mod_cast h
    rw [hcard]
    calc
      _ ≤ ∑ _p : (Fin (n+1) × Fin (detectorZeroBinCount e)) × Ray,
          C*(Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*
            (1+height)*K*(Z^d)^(jointCountExponent (2*a₀-1) δ+83*ε) :=
        Finset.sum_le_sum fun p _ => hchild p
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have := hbound.1
    positivity

/-- Whole selected-core count with the literal lower zero guard. The
analytic amplitude cutoff is `.5005`; if it exceeds the internally lowered
zero slope, the unit-column SC count is used. This allows density floor
any zero floor at least `3/4+e`, with all zero-bin errors explicit.
-/
theorem whole_core_zero_count (dmin dmax τ ε e κ η : ℝ) (n : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*η)
    (hε : 0 < ε) (hεsmall : ε ≤ 1/1000) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η ≤ ε/2)
    (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ (n : ℝ)*e) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    1 < Z^d → 2 < Z^τ →
    ∀ {Label Ray : Type*} [Fintype Label] [Fintype Ray]
      (E : Finset O) (χ : O → Label → Character) (ray : O → Ray)
      (hχ : ∀ u : E, ∀ j, (χ u.val j).residue ≠ 1)
      (base : Ray → Label → Ideal O → ℂ),
    (∀ z ∈ E, ∀ j J, idealCoeff (χ z j) J = base (ray z) j J * idealRowHom z J) →
    (∀ r j J, ‖base r j J‖ ≤ 1) →
    ∀ (b δ K Xmax height : ℝ), b ∈ Set.Icc ((3/4 : ℝ)+e) (7/8) →
    δ ∈ Set.Icc (500000001/1000000000 : ℝ) (3/4) →
    (∀ u : E, b ≤ HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (Z^τ)) →
    (∀ u : E, ∀ j, (χ u.val j).modulus.absNorm ≤ Z^d) →
    SelectedAllSourceNormBound E (Z^d) δ K Xmax → 6*(Z^d)^(3 : ℝ) ≤ Xmax →
    0 ≤ height → 2*Real.pi*(Z^d)^(τ/(2*dmax))+(3*n : ℕ)*Z^τ ≤ height →
    (E.card : ℝ) ≤ C*max 1 (((n+1 : ℕ) : ℝ)*(detectorZeroBinCount e : ℝ)*
      (Fintype.card Ray : ℝ)*(Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*(1+height))*
      K*(Z^d)^(detectorRate (2*b-1) δ+83*ε+2*e) := by
  obtain ⟨C, Z₀, hC, hcount⟩ := unpartitioned_core_zero_count dmin dmax τ ε e κ η n
    hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκ hκ' hη hbudget hn hwidth
  refine ⟨2+C, Z₀, by linarith, ?_⟩
  intro Z hZ d hd hd' hU hT Label Ray _ _ E χ ray hχ base hrow hbase
    b δ K Xmax height hb hδ hzero hconductor hbound hcap hh hfreq
  let F := (((n+1 : ℕ) : ℝ)*(detectorZeroBinCount e : ℝ)*
    (Fintype.card Ray : ℝ)*(Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*(1+height))
  have hUp : 0 < Z^d := zero_lt_one.trans hU
  have hK : 0 ≤ K := hbound.1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hmax : 1 ≤ max 1 F := le_max_left _ _
  have hrange : 2*(b-e)-1 ∈ Set.Icc (1/2 : ℝ) (3/4) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hrate := detectorRate_zero_buffer (show (1/2 : ℝ) ≤ δ by linarith [hδ.1])
    (show 2*b-1 ≤ 3/4 by linarith [hb.2]) he.le
  have hsame : 2*b-1-2*e = 2*(b-e)-1 := by ring
  rw [hsame] at hrate
  by_cases hbranch : δ ≤ 2*(b-e)-1
  · have h := hcount Z hZ d hd hd' hU hT E χ ray hχ base hrow hbase
      (b-e) δ K Xmax height hrange ⟨by linarith [hδ.1], hbranch⟩
      (by intro u; simpa only [sub_add_cancel] using hzero u)
      hconductor hbound hcap hh hfreq
    have hexp : jointCountExponent (2*(b-e)-1) δ+83*ε ≤
        detectorRate (2*b-1) δ+83*ε+2*e := by
      rw [detectorRate, ite_eq_left hbranch] at hrate
      linarith
    have hconst : C*F ≤ (2+C)*max 1 F := by
      have hfmax := le_max_right (1 : ℝ) F
      nlinarith
    have h' : (E.card : ℝ) ≤ C*F*K*(Z^d)^(jointCountExponent (2*(b-e)-1) δ+83*ε) := by
      simpa only [F, mul_assoc] using h
    exact h'.trans (mul_le_mul (mul_le_mul_of_nonneg_right hconst hK)
      (Real.rpow_le_rpow_of_exponent_le hU.le hexp) (by positivity) (by positivity))
  · have hXmax : 1 ≤ Xmax := by
      have hp := Real.one_le_rpow hU.le (by norm_num : (0 : ℝ) ≤ 3)
      linarith
    have h := selected_set_SC_count E (Z^d) δ K Xmax hU.le (by linarith [hδ.2]) hXmax hbound
    have hexp : 1-δ ≤ detectorRate (2*b-1) δ+83*ε+2*e := by
      rw [detectorRate, ite_eq_right hbranch] at hrate
      linarith
    have hconst : (2 : ℝ) ≤ (2+C)*max 1 F := by nlinarith
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right hconst hK)
      (Real.rpow_le_rpow_of_exponent_le hU.le hexp) (by positivity) (by positivity))

/-- Actual trivial count for all nonzero element rows in the natural norm
ball. It applies in particular to every selected free-core subset. -/
theorem nonzero_natural_row_count (E : Finset O) (U : ℝ) (hU : 1 ≤ U)
    (hnonzero : ∀ z ∈ E, z ≠ 0)
    (hnorm : ∀ z ∈ E, ((Ideal.span {z}).absNorm : ℝ) ≤ U) :
    (E.card : ℝ) ≤ 768*U := by
  have hi := DescentFiberCost.finite_ideal_count_real
    (E.image (fun z => Ideal.span {z})) U hU
    (by intro J hJ; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hJ
        exact Ideal.span_singleton_eq_bot.not.mpr (hnonzero z hz))
    (by intro J hJ; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hJ
        exact hnorm z hz)
  exact (CenteredExceptionalCount.element_count_le_six_ideal_count E hnonzero).trans
    ((mul_le_mul_of_nonneg_left hi (by norm_num)).trans_eq (by ring))

/-- The large-height complementary count fixes its degree using only the
compact conductor cap and the early auxiliary height exponent. The degree
is selected before every live height, dictionary, selected set, or slots. -/
theorem exists_large_height_count_degree (dmax τ : ℝ) (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ (Z d R T : ℝ) (E : Finset O), 1 ≤ Z → 0 ≤ d → d ≤ dmax → 0 ≤ R →
      Z^τ ≤ T →
      (∀ z ∈ E, z ≠ 0) →
      (∀ z ∈ E, ((Ideal.span {z}).absNorm : ℝ) ≤ Z^d) →
      (E.card : ℝ) ≤ 768*(1+T)^J*(Z^d)^R := by
  let J := ⌈dmax/τ⌉₊
  have hJ : dmax ≤ τ*(J : ℝ) := by
    have h := (div_le_iff₀ hτ).mp (Nat.le_ceil (dmax/τ))
    simpa only [mul_comm, J] using h
  refine ⟨J, ?_⟩
  intro Z d R T E hZ hd hdmax hR hT hnonzero hnorm
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hU : 1 ≤ Z^d := Real.one_le_rpow hZ hd
  have hTpos : 0 ≤ T := (Real.rpow_nonneg hZp.le τ).trans hT
  have hpower : Z^d ≤ (1+T)^J := by
    calc
      _ ≤ Z^(τ*(J : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ (hdmax.trans hJ)
      _ = (Z^τ)^J := by rw [Real.rpow_mul hZp.le, Real.rpow_natCast]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) J
  have hRpow : 1 ≤ (Z^d)^R := Real.one_le_rpow hU hR
  calc
    _ ≤ 768*(Z^d) := nonzero_natural_row_count E (Z^d) hU hnonzero hnorm
    _ ≤ 768*((1+T)^J) := mul_le_mul_of_nonneg_left hpower (by norm_num)
    _ ≤ _ := by nlinarith [pow_nonneg (show 0 ≤ 1+T by linarith) J]

/-- The complete sixth-root sum, including every ordinary nonzero ideal,
has a uniform constant for all joint count exponents at least `1/4`.
There is no coprimality or squarefree restriction on the root. -/
theorem uniform_sixth_root_sum : ∃ C : ℝ, 0 < C ∧
    ∀ (roots : Finset HeckeInverseAmplification.NonzeroIdeal) (B R : ℝ),
      0 ≤ B → (1/4 : ℝ) ≤ R →
      ∑ v ∈ roots, (B/(v.val.absNorm : ℝ)^6)^R ≤ C*B^R := by
  let weight : HeckeInverseAmplification.NonzeroIdeal → ℝ := fun v =>
    (v.val.absNorm : ℝ)^(-(3/2 : ℝ))
  have hnormpos (v : HeckeInverseAmplification.NonzeroIdeal) : 0 < (v.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.property)
  have hs : Summable weight := by
    have h := (CubicEisenstein.fullIdealWeight_summable_norm ((3/2 : ℝ) : ℂ) (by norm_num)).subtype
      (fun I : Ideal O => I ≠ 0)
    apply h.congr
    intro v
    change ‖CubicEisenstein.fullIdealWeight ((3/2 : ℝ) : ℂ) v.val‖ = weight v
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right v.property]
    change ‖((v.val.absNorm : ℝ) : ℂ)^(-((3/2 : ℝ) : ℂ))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hnormpos v)]
    simp only [Complex.neg_re, Complex.ofReal_re, weight]
  let C := 1+∑' v, weight v
  have hC : 0 < C := by
    have h : 0 ≤ ∑' v, weight v :=
      tsum_nonneg (fun v => Real.rpow_nonneg (hnormpos v).le (-(3/2 : ℝ)))
    dsimp [C, weight]
    linarith
  refine ⟨C, hC, ?_⟩
  intro roots B R hB hR
  have hweight (v : HeckeInverseAmplification.NonzeroIdeal) :
      (v.val.absNorm : ℝ)^(-(6*R)) ≤ weight v := by
    have hn : 1 ≤ (v.val.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.property)
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hid (v : HeckeInverseAmplification.NonzeroIdeal) :
      (B/(v.val.absNorm : ℝ)^6)^R = B^R*(v.val.absNorm : ℝ)^(-(6*R)) := by
    rw [Real.div_rpow hB (by positivity), ← Real.rpow_natCast_mul (hnormpos v).le,
      div_eq_mul_inv, Real.rpow_neg (hnormpos v).le]
    norm_num
  calc
    _ = B^R * ∑ v ∈ roots, (v.val.absNorm : ℝ)^(-(6*R)) := by
      simp_rw [hid]
      rw [Finset.mul_sum]
    _ ≤ B^R * ∑ v ∈ roots, weight v :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hweight v) (by positivity)
    _ ≤ B^R * ∑' v, weight v := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum roots (fun v _ => Real.rpow_nonneg (hnormpos v).le _) hs) (by positivity)
    _ ≤ _ := by
      have hp : 0 ≤ B^R := Real.rpow_nonneg hB _
      dsimp [C]
      nlinarith

/-- Exact natural-row reassembly, allowing a DIFFERENT selected predicate
for each sixth root. Thus a common root mask may change the selected core
family. This is a finite count reassembly lemma, not an analytic count input:
the free counts must be supplied by the preceding operator/detector theorem.
Every unit, shared-prime state and ordinary root ideal is retained.
-/
theorem natural_root_count_of_uniform_free_counts :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : HeckeInverseAmplification.NonzeroIdeal →
        HeckeInverseAmplification.FreeRow → Prop) (C R : ℝ), 0 ≤ C → (1/4 : ℝ) ≤ R →
      (∀ (v : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ), 1 ≤ Y →
        ∀ F : Finset HeckeInverseAmplification.FreeRow,
        (∀ u ∈ F, ProbeHighRowFamily.rowNorm u ≤ Y ∧ P v u) →
        (F.card : ℝ) ≤ C*Y^R) →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset ProbePhysical.NonzeroFrequency,
      (∀ h ∈ rows, LocalMoment.rawFrequencyNorm h ≤ H ∧
        P (ProbePhysical.sixthFrequencyEquiv.symm h).2 (ProbePhysical.sixthFrequencyEquiv.symm h).1) →
      (rows.card : ℝ) ≤ C*D*H^R := by
  open HeckeInverseAmplification LocalMoment ProbePhysical ProbeHighRowFamily in
  obtain ⟨D, hD, hsum⟩ := uniform_sixth_root_sum
  refine ⟨D, hD, ?_⟩
  intro P C R hC hR hfree H hH rows hrows
  open HeckeInverseAmplification LocalMoment ProbePhysical ProbeHighRowFamily in
  have hfiber (v : HeckeInverseAmplification.NonzeroIdeal) :
      ((sixthFreeFiber rows v).card : ℝ) ≤ C*(H/(v.val.absNorm : ℝ)^6)^R := by
    have hnv : 0 < (v.val.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.property)
    have hmem (u : FreeRow) (hu : u ∈ sixthFreeFiber rows v) :
        rowNorm u ≤ H/(v.val.absNorm : ℝ)^6 ∧ P v u := by
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
      obtain ⟨hp, hpv⟩ := Finset.mem_filter.mp hp
      have he : p = (u,v) := Prod.ext hpu hpv
      subst p
      have hr := hrows _ ((mem_sixthPairs rows (u,v)).mp hp)
      rw [raw_sixth_norm] at hr
      exact ⟨(le_div_iff₀ (pow_pos hnv 6)).mpr hr.1,
        by simpa only [Equiv.symm_apply_apply] using hr.2⟩
    by_cases hY : 1 ≤ H/(v.val.absNorm : ℝ)^6
    · exact hfree v _ hY _ hmem
    · have he : sixthFreeFiber rows v = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact hY ((rowNorm_ge_one u).trans (hmem u hu).1)
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  open HeckeInverseAmplification LocalMoment ProbePhysical ProbeHighRowFamily in
  have hc : (rows.card : ℝ) ≤ ∑ v ∈ (sixthPairs rows).image Prod.snd,
      C*(H/(v.val.absNorm : ℝ)^6)^R := by
    rw [raw_sixth_cardinality rows, Nat.cast_sum]
    exact Finset.sum_le_sum fun v _ => hfiber v
  calc
    _ ≤ C*∑ v ∈ (LocalMoment.sixthPairs rows).image Prod.snd,
        (H/(v.val.absNorm : ℝ)^6)^R := by simpa only [Finset.mul_sum] using hc
    _ ≤ C*(D*H^R) := mul_le_mul_of_nonneg_left (hsum _ H R hH.le hR) hC
    _ = _ := by ring

/-- Every natural row with small sixth-free core is counted here, including
all overlapping core/root primes. A deliberately coarse `B^(13/60)` bound
already fits under every retained joint exponent `R ≥ 1/4`. -/
theorem small_sixth_core_count (E : Finset O) (B H : ℝ) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hnonzero : ∀ z ∈ E, z ≠ 0)
    (hnorm : ∀ z ∈ E, ((Ideal.span {z}).absNorm : ℝ) ≤ B)
    (hcore : ∀ z ∈ E, ((CenteredExceptionalCount.sixthRemainder (Ideal.span {z})).absNorm : ℝ) ≤ H) :
    (E.card : ℝ) ≤ 98304*H*B^(1/6 : ℝ) := by
  let core (z : O) := CenteredExceptionalCount.sixthRemainder (Ideal.span {z})
  let cores := E.image core
  have hcores : (cores.card : ℝ) ≤ 128*H := DescentFiberCost.finite_ideal_count_real cores H hH
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact CenteredExceptionalCount.sixthRemainder_ne_zero _)
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hcore z hz)
  have hchild (I : Ideal O) (hI : I ∈ cores) :
      ((E.filter fun z => core z = I).card : ℝ) ≤ 768*B^(1/6 : ℝ) := by
    have hI0 : I ≠ 0 := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact CenteredExceptionalCount.sixthRemainder_ne_zero _
    have hnI : 1 ≤ (I.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
    have h := CenteredExceptionalCount.element_count_fixed_remainder
      (E.filter fun z => core z = I) I hI0 B (by linarith)
      (fun z hz => hnonzero z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hnorm z (Finset.mem_filter.mp hz).1)
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ (by linarith : 0 < (I.absNorm : ℝ))).2
        (by nlinarith)) (by norm_num : (0 : ℝ) ≤ 1/6)) (by norm_num))
  have hcard : (E.card : ℝ) = ∑ I ∈ cores, ((E.filter fun z => core z = I).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := cores) (f := core)
      (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    exact_mod_cast h
  calc
    _ = ∑ I ∈ cores, ((E.filter fun z => core z = I).card : ℝ) := hcard
    _ ≤ ∑ _I ∈ cores, 768*B^(1/6 : ℝ) := Finset.sum_le_sum fun I hI => hchild I hI
    _ = (cores.card : ℝ)*(768*B^(1/6 : ℝ)) := by simp
    _ ≤ (128*H)*(768*B^(1/6 : ℝ)) := mul_le_mul_of_nonneg_right hcores (by positivity)
    _ = _ := by ring

theorem small_sixth_core_count_le_joint (E : Finset O) (B R : ℝ) (hB : 1 ≤ B)
    (hR : (1/4 : ℝ) ≤ R) (hnonzero : ∀ z ∈ E, z ≠ 0)
    (hnorm : ∀ z ∈ E, ((Ideal.span {z}).absNorm : ℝ) ≤ B)
    (hcore : ∀ z ∈ E, ((CenteredExceptionalCount.sixthRemainder (Ideal.span {z})).absNorm : ℝ) ≤ B^(1/20 : ℝ)) :
    (E.card : ℝ) ≤ 98304*B^R := by
  have h := small_sixth_core_count E B (B^(1/20 : ℝ)) hB
    (Real.one_le_rpow hB (by norm_num)) hnonzero hnorm hcore
  have hUp : 0 < B := zero_lt_one.trans_le hB
  have heq : (B^(1/20 : ℝ))*B^(1/6 : ℝ) = B^(13/60 : ℝ) := by
    rw [← Real.rpow_add hUp]
    norm_num
  calc
    _ ≤ 98304*(B^(1/20 : ℝ))*B^(1/6 : ℝ) := h
    _ = 98304*B^(13/60 : ℝ) := by rw [mul_assoc, heq]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by norm_num)

/-- Equality of actual buffered zero maxima from equality of the positive
half-plane zero events. This transports events, not just individual zeros. -/
theorem zeroMaximum_eq_of_positive_zeros {Label : Type*} [Fintype Label]
    (χ ψ : Label → Character) (hχ : ∀ j, (χ j).residue ≠ 1)
    (hψ : ∀ j, (ψ j).residue ≠ 1) (T : ℝ)
    (hzero : ∀ j (s : ℂ), 0 < s.re → (LFunction (χ j) s = 0 ↔ LFunction (ψ j) s = 0)) :
    HeckeDetectorZeros.zeroMaximum χ hχ T = HeckeDetectorZeros.zeroMaximum ψ hψ T := by
  have hle (ξ ζ : Label → Character) (hξ : ∀ j, (ξ j).residue ≠ 1)
      (hζ : ∀ j, (ζ j).residue ≠ 1)
      (hz : ∀ j (s : ℂ), 0 < s.re → (LFunction (ξ j) s = 0 → LFunction (ζ j) s = 0)) :
      HeckeDetectorZeros.zeroMaximum ξ hξ T ≤ HeckeDetectorZeros.zeroMaximum ζ hζ T := by
    rcases lt_or_ge (51/100 : ℝ) (HeckeDetectorZeros.zeroMaximum ξ hξ T) with hm | hm
    · obtain ⟨j, s, hsz, ht, hs⟩ := HeckeDetectorZeros.maximum_attained ξ hξ T hm
      rw [← hs]
      exact HeckeDetectorZeros.zero_re_le_maximum ζ hζ T j
        (by linarith [hm]) ht (hz j s (by linarith [hm]) hsz)
    · exact hm.trans (HeckeDetectorZeros.zeroMaximum_bounds ζ hζ T).1
  exact le_antisymm (hle χ ψ hχ hψ (fun j s hs => (hzero j s hs).mp))
    (hle ψ χ hψ hχ (fun j s hs => (hzero j s hs).mpr))

/-- Removing a fixed natural-root Euler mask changes no positive-half-plane
zero event. It does not enlarge the free presentation's primitive conductor. -/
theorem zeroMaximum_mask_eq_free {Label : Type*} [Fintype Label]
    (natural free : Label → Character) (hnatural : ∀ j, (natural j).residue ≠ 1)
    (hfree : ∀ j, (free j).residue ≠ 1) (T : ℝ)
    (hmask : ∀ j (I : Ideal O), idealCoeff (natural j) I =
      if IsCoprime I (natural j).modulus then idealCoeff (free j) I else 0) :
    HeckeDetectorZeros.zeroMaximum natural hnatural T = HeckeDetectorZeros.zeroMaximum free hfree T := by
  apply zeroMaximum_eq_of_positive_zeros natural free hnatural hfree T
  intro j s hs
  rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal (natural j) (free j)
    (hmask j) (hnatural j) hs, mul_eq_zero]
  exact or_iff_left (HeckeFiniteDeletion.factors_ne_zero (natural j).modulus (free j) hs)

private def detectorNonprincipal (χ : Character) : Prop := χ.residue ≠ 1

/-- Each dictionary entry may use either of the two genuine orientations.
Conjugation transports the whole zero event with the same real part and
absolute height; no arbitrary-power natural-row assertion is used. -/
theorem zeroMaximum_oriented_eq {Label : Type*} [Fintype Label]
    (χ : Label → Character) (hχ : ∀ j, (χ j).residue ≠ 1)
    (reverse : Label → Bool) (T : ℝ) :
    let ψ := fun j => if reverse j then (χ j).inverse else χ j
    let hψ : ∀ j, detectorNonprincipal (ψ j) := fun j => by
      change detectorNonprincipal (if reverse j then (χ j).inverse else χ j)
      by_cases hj : reverse j = true
      · rw [ite_eq_left hj]
        exact HeckeDetectorFamilyInclusion.inverse_nonprincipal (χ j) (hχ j)
      · rw [ite_eq_right hj]
        exact hχ j
    HeckeDetectorZeros.zeroMaximum ψ hψ T = HeckeDetectorZeros.zeroMaximum χ hχ T := by
  dsimp only
  let ψ := fun j => if reverse j then (χ j).inverse else χ j
  have hψ : ∀ j, detectorNonprincipal (ψ j) := by
    intro j
    change detectorNonprincipal (if reverse j then (χ j).inverse else χ j)
    by_cases hj : reverse j = true
    · rw [ite_eq_left hj]
      exact HeckeDetectorFamilyInclusion.inverse_nonprincipal (χ j) (hχ j)
    · rw [ite_eq_right hj]
      exact hχ j
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (HeckeDetectorZeros.zeroMaximum ψ hψ T) with hm | hm
    · obtain ⟨j, s, hz, ht, hs⟩ := HeckeDetectorZeros.maximum_attained ψ hψ T hm
      by_cases hj : reverse j = true
      · change LFunction (if reverse j then (χ j).inverse else χ j) s = 0 at hz
        rw [ite_eq_left hj, HeckeFamily.LFunction_inverse_conj (χ j) (hχ j)] at hz
        have hz' : LFunction (χ j) (star s) = 0 := (map_eq_zero (starRingEnd ℂ)).mp hz
        have h := HeckeDetectorZeros.zero_re_le_maximum χ hχ T j
          (s := star s) (by simpa only [Complex.star_def, Complex.conj_re, hs] using hm.le) (by simpa using ht) hz'
        simpa only [Complex.star_def, Complex.conj_re, hs] using h
      · have hz' : LFunction (χ j) s = 0 := by simpa only [ψ, hj, Bool.false_eq_true, ite_false] using hz
        rw [← hs]
        exact HeckeDetectorZeros.zero_re_le_maximum χ hχ T j (by linarith) ht hz'
    · exact hm.trans (HeckeDetectorZeros.zeroMaximum_bounds χ hχ T).1
  · rcases lt_or_ge (51/100 : ℝ) (HeckeDetectorZeros.zeroMaximum χ hχ T) with hm | hm
    · obtain ⟨j, s, hz, ht, hs⟩ := HeckeDetectorZeros.maximum_attained χ hχ T hm
      by_cases hj : reverse j = true
      · have hz' : LFunction (ψ j) (star s) = 0 := by
          dsimp [ψ]
          rw [ite_eq_left hj, HeckeFamily.LFunction_inverse_conj (χ j) (hχ j)]
          simpa using hz
        have h := HeckeDetectorZeros.zero_re_le_maximum ψ hψ T j
          (s := star s) (by simpa only [Complex.star_def, Complex.conj_re, hs] using hm.le) (by simpa using ht) hz'
        simpa only [Complex.star_def, Complex.conj_re, hs] using h
      · have hz' : LFunction (ψ j) s = 0 := by simpa only [ψ, hj, Bool.false_eq_true, ite_false] using hz
        rw [← hs]
        exact HeckeDetectorZeros.zero_re_le_maximum ψ hψ T j (by linarith) ht hz'
    · exact hm.trans (HeckeDetectorZeros.zeroMaximum_bounds ψ hψ T).1

end
end Qrh.JointDetector.FrontierDetectorCount

#print axioms Qrh.JointDetector.FrontierDetectorCount.uniform_supported_core_count
#print axioms Qrh.JointDetector.FrontierDetectorCount.buffered_core_zero_count
#print axioms Qrh.JointDetector.FrontierDetectorCount.unpartitioned_core_zero_count
#print axioms Qrh.JointDetector.FrontierDetectorCount.selected_set_SC_count
#print axioms Qrh.JointDetector.FrontierDetectorCount.SC_energy_le_refined_g
#print axioms Qrh.JointDetector.FrontierDetectorCount.zeroMaximum_mask_eq_free
#print axioms Qrh.JointDetector.FrontierDetectorCount.zeroMaximum_oriented_eq
#print axioms Qrh.JointDetector.FrontierDetectorCount.exists_large_height_count_degree
#print axioms Qrh.JointDetector.FrontierDetectorCount.uniform_sixth_root_sum
#print axioms Qrh.JointDetector.FrontierDetectorCount.small_sixth_core_count_le_joint
#print axioms Qrh.JointDetector.FrontierDetectorCount.whole_core_zero_count
#print axioms Qrh.JointDetector.FrontierDetectorCount.natural_root_count_of_uniform_free_counts
