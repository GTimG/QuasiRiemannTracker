import Cycle25.Numerator.Imported.NumeratorRamifiedProduct
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Absolute Mellin coefficient packet for the original complete correction. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem weighted_product_term {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ) (i : ι) (j : κ) :
    ‖A i * B j‖ * ((N i * M j : ℝ≥0) : ℝ) ^ (-sigma) =
      (‖A i‖ * (N i : ℝ) ^ (-sigma)) * (‖B j‖ * (M j : ℝ) ^ (-sigma)) := by
  rw [norm_mul, NNReal.coe_mul, Real.mul_rpow (show (0 : ℝ) ≤ N i from (N i).property) (show (0 : ℝ) ≤ M j from (M j).property)]
  ring

theorem mellin_product_term {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (w : ℂ) (i : ι) (j : κ) :
    (A i * B j) * ((N i * M j : ℝ≥0) : ℂ) ^ (-w) =
      (A i * (N i : ℂ) ^ (-w)) * (B j * (M j : ℂ) ^ (-w)) := by
  have hh := map_mul (positiveCpowHom (-w)) (N i) (M j)
  simp only [positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
  rw [hh]
  ring

theorem weighted_product_summable {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ)
    (hA : Summable (fun i => ‖A i‖ * (N i : ℝ) ^ (-sigma)))
    (hB : Summable (fun i => ‖B i‖ * (M i : ℝ) ^ (-sigma))) :
    Summable (fun ij : ι × κ => ‖A ij.1 * B ij.2‖ *
      ((N ij.1 * M ij.2 : ℝ≥0) : ℝ) ^ (-sigma)) := by
  simp_rw [weighted_product_term]
  exact hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity)

theorem weighted_product_mass {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ)
    (hA : Summable (fun i => ‖A i‖ * (N i : ℝ) ^ (-sigma)))
    (hB : Summable (fun i => ‖B i‖ * (M i : ℝ) ^ (-sigma))) :
    (∑' ij : ι × κ, ‖A ij.1 * B ij.2‖ * ((N ij.1 * M ij.2 : ℝ≥0) : ℝ) ^ (-sigma)) =
      (∑' i, ‖A i‖ * (N i : ℝ) ^ (-sigma)) *
      (∑' j, ‖B j‖ * (M j : ℝ) ^ (-sigma)) := by
  simp_rw [weighted_product_term]
  exact (hA.tsum_mul_tsum hB
    (hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity))).symm

def CorrectionIndex (S : Finset (Ideal O)) (u : FreeRow) :=
  (ramifiedPrimes S u → Fin 3) × EulerIndex {P : PrimeIdeal // P.val ∉ S} 3

def correctionCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (e : CorrectionIndex S u) : ℂ :=
  ramifiedTupleCoefficient S hS η u x z e.1 *
    eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e.2

def correctionScale (S : Finset (Ideal O)) (u : FreeRow) (e : CorrectionIndex S u) : ℝ≥0 :=
  ramifiedTupleScale S u e.1 * eulerScale (fun P => primeScale P.val) e.2

theorem ramifiedTupleScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (j : ramifiedPrimes S u → Fin 3) : 1 ≤ ramifiedTupleScale S u j := by
  apply Finset.one_le_prod
  intro P hP
  exact one_le_pow₀ (primeScale_one_le P.val)

theorem correctionScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (e : CorrectionIndex S u) : 1 ≤ correctionScale S u e := by
  unfold correctionScale
  exact one_le_mul_of_one_le_of_one_le (ramifiedTupleScale_one_le S u e.1)
    (eulerScale_one_le (fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val)
      (fun P => primeScale_one_le P.val) e.2)

theorem continuedCorrection_coefficient_mass (eps sigma : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
    (x z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hsigma : -(1 / 100 : ℝ) ≤ sigma) (hxw : 1 + eps ≤ x.re + sigma) :
    Summable (fun e : CorrectionIndex S u => ‖correctionCoefficient S hS η u x z e‖ *
      (correctionScale S u e : ℝ) ^ (-sigma)) ∧
    (∑' e : CorrectionIndex S u, ‖correctionCoefficient S hS η u x z e‖ *
      (correctionScale S u e : ℝ) ^ (-sigma)) ≤
      579 ^ (ramifiedPrimes S u).card * Real.exp (1 / 2) := by
  obtain ⟨hU,hUm⟩ := actual_unramified_coefficient_mass eps sigma S hfirst η u x z hx hz hsigma hxw
  have hR := ramified_product_coefficient_mass S hS η u x z sigma hx hsigma hz
    (by linarith [hfirst.positive])
  have hRs := (hasSum_fintype (fun j : ramifiedPrimes S u → Fin 3 =>
    ‖ramifiedTupleCoefficient S hS η u x z j‖ * (ramifiedTupleScale S u j : ℝ) ^ (-sigma))).summable
  refine ⟨weighted_product_summable _ _ _ _ sigma hRs hU, ?_⟩
  change (∑' e : (ramifiedPrimes S u → Fin 3) × EulerIndex {P : PrimeIdeal // P.val ∉ S} 3,
    ‖ramifiedTupleCoefficient S hS η u x z e.1 *
      eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e.2‖ *
    ((ramifiedTupleScale S u e.1 * eulerScale (fun P => primeScale P.val) e.2 : ℝ≥0) : ℝ) ^ (-sigma)) ≤ _
  rw [weighted_product_mass _ _ _ _ sigma hRs hU, tsum_fintype]
  exact mul_le_mul hR hUm (tsum_nonneg (fun _ => by positivity)) (by positivity)

theorem continuedCorrection_coefficient_expansion (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    continuedCorrection S hS η u x w z =
      ∑' e : CorrectionIndex S u, correctionCoefficient S hS η u x z e *
        (correctionScale S u e : ℂ) ^ (-w) := by
  have hU := (actual_unramified_coefficient_mass eps w.re S hfirst η u x z hx hz hw hxw).1
  have hUn : Summable (fun e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3 =>
      ‖eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e *
        (eulerScale (fun P => primeScale P.val) e : ℂ) ^ (-w)‖) := by
    convert hU using 1
    ext e
    have hp : 0 < (eulerScale (fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val) e : ℝ) := by
      have hh := eulerScale_one_le (fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val)
        (fun P => primeScale_one_le P.val) e
      exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re]
  rw [continuedCorrection, ramified_product_expansion,
    actual_unramified_expansion eps S hfirst η u x w z hx hz hw hxw]
  have hprod := tsum_mul_tsum_of_summable_norm
    (hasSum_fintype (fun j : ramifiedPrimes S u → Fin 3 =>
      ‖ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w)‖)).summable hUn
  simp only [tsum_fintype] at hprod
  rw [hprod]
  apply tsum_congr
  intro e
  exact (mellin_product_term _ _ _ _ w e.1 e.2).symm

theorem continuedCorrection_coefficient_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (eps sigma : ℝ) (S : Finset (Ideal O))
      (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (x z : ℂ), (51 / 100 : ℝ) ≤ x.re → (17 / 50 : ℝ) ≤ z.re →
      -(1 / 100 : ℝ) ≤ sigma → 1 + eps ≤ x.re + sigma →
      (∑' e : CorrectionIndex S u, ‖correctionCoefficient S hS η u x z e‖ *
        (correctionScale S u e : ℝ) ^ (-sigma)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ epsilon := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 579 epsilon
    (by norm_num) hepsilon
  refine ⟨C * Real.exp (1 / 2), by positivity, ?_⟩
  intro eps sigma S hS hfirst η u x z hx hz hsigma hxw
  have hm := (continuedCorrection_coefficient_mass eps sigma S hS hfirst η u x z
    hx hz hsigma hxw).2
  have hc : (579 : ℝ) ^ (ramifiedPrimes S u).card ≤
      C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ epsilon := by
    apply le_trans _ (hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
    apply pow_le_pow_right₀ (by norm_num)
    rw [←HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  exact hm.trans ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq (by ring))

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
