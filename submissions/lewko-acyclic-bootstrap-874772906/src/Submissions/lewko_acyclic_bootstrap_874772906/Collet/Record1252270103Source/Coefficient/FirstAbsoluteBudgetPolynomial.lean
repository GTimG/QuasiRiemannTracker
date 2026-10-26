/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite absolute Gauss bounds for every first Mellin height. The actual
normalization and supported-column restriction are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondAbsoluteEnvelopeRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondAbsoluteEnvelopeMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstChildPolynomial
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.GaussNormalization
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstAbsoluteBudget
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentAddedZero CenteredMomentAbsoluteEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem source_polynomial_norm (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (τ:Character) (t Y:ℝ) (hY:0≤Y)
    (hcap:∀I∈S,β I≠0→(I.absNorm:ℝ)≤Y) (z:O) :
    ‖gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>β I*rowWeight τ fixedBadMask 1 1 t I) z‖≤
      Real.sqrt Y*(∑I∈S,‖β I‖) := by
  have hpoint (I:supportedColumns S) :
      ‖(β I*rowWeight τ fixedBadMask 1 1 t I)*
        gaussRow (sourceGenerator S I) (sourceGenerator_supported S I) z‖≤Real.sqrt Y*‖β I‖ := by
    by_cases hb:β I=0
    · simp only [hb,zero_mul,norm_zero,mul_zero,le_refl]
    have hg:=gaussRow_norm_le (sourceGenerator S I) (sourceGenerator_supported S I) z
    have hspan:Ideal.span {sourceGenerator S I}=(I:Ideal O) :=
      primary_span_supported I (Finset.mem_filter.mp I.property).2
    rw [hspan] at hg
    have hg':‖gaussRow (sourceGenerator S I) (sourceGenerator_supported S I) z‖≤Real.sqrt Y :=
      hg.trans (Real.sqrt_le_sqrt (hcap I (Finset.mem_filter.mp I.property).1 hb))
    rw [norm_mul,norm_mul]
    exact (mul_le_mul
      (mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all τ fixedBadMask 1 1 t I))
      hg' (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  unfold gaussPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _≤∑I:supportedColumns S,Real.sqrt Y*‖β I‖ := Finset.sum_le_sum (fun I _=>hpoint I)
    _=Real.sqrt Y*∑I∈supportedColumns S,‖β I‖ := by
      rw [←Finset.mul_sum]
      exact congrArg (fun x=>Real.sqrt Y*x)
        (Finset.sum_coe_sort (supportedColumns S) (fun I:Ideal O=>‖β I‖))
    _≤_ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>norm_nonneg _))
      (Real.sqrt_nonneg _)

theorem normalized_source_polynomial_sq (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (τ:Character) (t Y T:ℝ) (hY:0≤Y) (hT:0<T)
    (hcap:∀I∈S,β I≠0→(I.absNorm:ℝ)≤Y) (z:O) :
    ‖gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>(Real.sqrt T:ℂ)⁻¹*(β I*rowWeight τ fixedBadMask 1 1 t I)) z‖^2≤
      Y/T*(∑I∈S,‖β I‖)^2 := by
  rw [gaussPolynomial_const_mul,norm_mul,mul_pow,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  have h:=pow_le_pow_left₀ (norm_nonneg _) (source_polynomial_norm S β τ t Y hY hcap z) 2
  rw [mul_pow,Real.sq_sqrt hY] at h
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hT.le)).trans_eq (by ring)

theorem normalized_dyadic_source (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (τ:Character) (t Y T X:ℝ) (hY:0≤Y) (hT:0<T) (hX:1≤X)
    (hcap:∀I∈S,β I≠0→(I.absNorm:ℝ)≤Y) (n:ℤ) (hscale:dyadicScale n≤X) :
    (∑'z:O,dyadicWeight n (normValue z)*
      ‖gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I:supportedColumns S=>(Real.sqrt T:ℂ)⁻¹*(β I*rowWeight τ fixedBadMask 1 1 t I)) z‖^2)≤
      diagonalControl ballProfile*X*(Y/T*(∑I∈S,‖β I‖)^2) := by
  apply (dyadic_energy_le_sum n _).trans
  calc
    _≤∑_z∈dyadRows n,Y/T*(∑I∈S,‖β I‖)^2 :=
      Finset.sum_le_sum (fun z _=>normalized_source_polynomial_sq S β τ t Y T hY hT hcap z)
    _=((dyadRows n).card:ℝ)*(Y/T*(∑I∈S,‖β I‖)^2) := by simp
    _≤_ := mul_le_mul_of_nonneg_right
      (SecondAbsoluteEnvelope.lattice_rows_card (dyadRows n) X hX
        (fun z hz=>(dyadRows_norm_lt n z hz).le.trans hscale)) (by positivity)

end
end QRH.Record1252270103Source.FirstAbsoluteBudget
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.source_polynomial_norm
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.normalized_source_polynomial_sq
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.normalized_dyadic_source
