/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal exceptional selector gives the same inducing class after every
nonzero puncture; compact radial support supplies the actual completed radius. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentChildRows CenteredMomentSecondHeightFamily
open CenteredMomentSecondReducedPredicate CenteredMomentSecondRadicalBudget CenteredMomentSectorLocalization
open CenteredExceptionalProfile HeckeRowClosure RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O

lemma corrected_row_conductor_bound (η : Character) (χ : RayCharacter) (R : Ideal O) (A z : O) :
    rowConductorBound (childCharacter η χ) (fixedBadMask*idealGenerator R) 1 (A*z)≤
      η.modulus.absNorm*fixedFactor*R.absNorm*(Ideal.span {A}).absNorm*(Ideal.span {z}).absNorm := by
  calc
    _=(childCharacter η χ).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*R.absNorm*(Ideal.span {A}).absNorm*(Ideal.span {z}).absNorm := by
      simp only [rowConductorBound,←Ideal.span_singleton_mul_span_singleton,
        span_idealGenerator,map_mul,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow]
      ring
    _≤(η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*R.absNorm*(Ideal.span {A}).absNorm*(Ideal.span {z}).absNorm := by
      gcongr
      exact child_modulus_bound η χ
    _=_ := by unfold fixedFactor;ring

lemma radial_norm_of_nonzero (Φ : 𝓢(ℝ,ℂ)) (b H : ℝ)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic b) (hH : 0<H) (z : O)
    (hn : (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0) :
    ((Ideal.span {z}).absNorm:ℝ)≤b*H := by
  have hn' : Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)≠0 := by
    intro h
    exact hn (by rw [h];rfl)
  have hsupport := hs hn'
  have hnorm := (div_le_iff₀ hH).mp hsupport
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hnorm
  exact hnorm

lemma corrected_conductor_polynomial (η : Character) (χ : RayCharacter) (R : Ideal O) (A z : O)
    (Z b H Bη BR BA BH : ℝ) (hZ : 0<Z) (hb : 0≤b) (hH : 0≤H)
    (hη : (η.modulus.absNorm:ℝ)≤Z^Bη) (hR : (R.absNorm:ℝ)≤Z^BR)
    (hA : ((Ideal.span {A}).absNorm:ℝ)≤Z^BA) (hscale : H≤Z^BH)
    (hrow : ((Ideal.span {z}).absNorm:ℝ)≤b*H)
    (hfixed : (fixedFactor:ℝ)*b≤Z) :
    (rowConductorBound (childCharacter η χ) (fixedBadMask*idealGenerator R) 1 (A*z):ℝ)≤
      Z^(Bη+BR+BA+BH+1) := by
  have hbase : (rowConductorBound (childCharacter η χ) (fixedBadMask*idealGenerator R) 1 (A*z):ℝ)≤
      (η.modulus.absNorm:ℝ)*fixedFactor*R.absNorm*(Ideal.span {A}).absNorm*(Ideal.span {z}).absNorm := by
    exact_mod_cast corrected_row_conductor_bound η χ R A z
  calc
    _≤(η.modulus.absNorm:ℝ)*fixedFactor*R.absNorm*(Ideal.span {A}).absNorm*(b*H) := by
      apply hbase.trans
      gcongr
    _≤Z^Bη*fixedFactor*Z^BR*Z^BA*(b*Z^BH) := by gcongr
    _=((fixedFactor:ℝ)*b)*(Z^Bη*Z^BR*Z^BA*Z^BH) := by ring
    _≤Z*(Z^Bη*Z^BR*Z^BA*Z^BH) := mul_le_mul_of_nonneg_right hfixed (by positivity)
    _=Z^(1:ℝ)*(Z^Bη*Z^BR*Z^BA*Z^BH) := by rw [Real.rpow_one]
    _=Z^(Bη+BR+BA+BH+1) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
      congr 1
      ring

/-- This is the actual selector in the exceptional second-child kernel.
The radius exponent is log_Z H itself, so no saving from retained radius is lost. -/
theorem corrected_selector_row_geometry (Q : Ideal O) (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (R : Ideal O) (hR0 : R≠0) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z b H Bη BR BA BH : ℝ) (hZ : 1<Z) (hb : 0≤b) (hH : 0<H)
    (Φ : 𝓢(ℝ,ℂ)) (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic b)
    (hη : (η.modulus.absNorm:ℝ)≤Z^Bη) (hR : (R.absNorm:ℝ)≤Z^BR)
    (hA : ((Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}).absNorm:ℝ)≤Z^BA)
    (hscale : H≤Z^BH) (hfixed : (fixedFactor:ℝ)*b≤Z) :
    CorrectedRowGeometry Q η χ C D U R Z (Bη+BR+BA+BH+1) b (Real.logb Z H)
      (fun z=>z≠0 ∧ FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) Φ H := by
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  have hA0 : A≠0 := mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hmR : fixedBadMask*idealGenerator R≠0 :=
    mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R hR0)
  refine ⟨fun z hz _=>hz.1,?_,?_,?_⟩
  · intro z hz hw
    exact (fixed_mask_change (childCharacter η χ) Q m (fixedBadMask*idealGenerator R) A z
      hm hmR hA0 hz.1 hmLam hm2
      ((dvd_mul_right goodLambda (2:O)).trans (dvd_mul_right fixedBadMask (idealGenerator R)))
      ((dvd_mul_left (2:O) goodLambda).trans (dvd_mul_right fixedBadMask (idealGenerator R)))).mp hz.2
  · intro z hz hw
    exact corrected_conductor_polynomial η χ R A z Z b H Bη BR BA BH
      (zero_lt_one.trans hZ) hb hH.le hη hR hA hscale (radial_norm_of_nonzero Φ b H hs hH z hw) hfixed
  · intro z hz hw
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hH]
    exact radial_norm_of_nonzero Φ b H hs hH z hw
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_row_conductor_bound
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_selector_row_geometry
