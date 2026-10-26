/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual nonzero retained block supplies the unclipped radius and canonical
partition. Its exceptional payment then has inverse-square radical decay. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalRadical
import Submissions.hailey_collet_1252270103.Cycle61.Physical.FinalNatural.State

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalLedger
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedWidth
open CenteredMomentSectorLocalization Cycle61FinalNatural
local notation "O" => ActualEisensteinCubic.O

theorem radial_scalar_bound (a c d f F R r : ℝ)
    (hc : 0<c) (hd : 0<d) (hf : 0<f) (hF : 0<F) (hR : 0<R)
    (hs : a/(c*d*F^(1/6:ℝ)*f^(2/3:ℝ))≤r^(-2:ℝ)) :
    a*(4*R/F)^(1/6:ℝ)/(c*d*f^(2/3:ℝ))≤(4*R)^(1/6:ℝ)*r^(-2:ℝ) := by
  have h:=mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (by positivity : 0≤4*R) (1/6:ℝ))
  rw [Real.div_rpow (by positivity : 0≤4*R) hF.le]
  convert h using 1 <;> ring

/-- The max-one radial enlargement is exactly the divided radius on every
nonzero original physical block. Zero blocks need no such assertion. -/
theorem actual_retained_radical_cost (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (hrows : ∀z∈rows,z≠0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (Z : ℝ) (hZ : 1<Z) :
    normalizer C D U*(retainedScale R C D U)^(1/6:ℝ)/
      ((C.absNorm:ℝ)*(D.absNorm:ℝ)*(forcingNorm C D U)^(2/3:ℝ))≤
      (4*R)^(1/6:ℝ)*(Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(-2:ℝ) := by
  obtain ⟨z,hz⟩:=actual_retained_witness t S β R rows W K n hne
  have hgeo:=retained_geometry R (commonFrequencyGenerator C D)
    (nonunitFrequencyGenerator C D U) z hz
  obtain ⟨w,hw,hpart,hcorr⟩:=physicalBlock_canonical_witness η t S β C D hC hD hCD
    U R rows hrows W K hK n hne
  have hc : (0:ℝ)<C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd : (0:ℝ)<D.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hf : 0<forcingNorm C D U:=common_product_pos C D hC _
  have hF : (0:ℝ)<Ideal.absNorm
      (Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hgeo.2.1 hgeo.2.2.1)))
  have hscalar:=actual_radical_scalar_bound C D hC hD hCD U
    (nonunitFrequencyGenerator C D U*w) hpart Z hZ
  have hh:=radial_scalar_bound (normalizer C D U) (C.absNorm:ℝ) (D.absNorm:ℝ)
    (forcingNorm C D U)
    (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}):ℝ)
    R (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ) hc hd hf hF hgeo.1 hscalar
  have hscale : retainedScale R C D U=4*R/
      (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}):ℝ) := by
    rw [retainedScale,max_eq_right hgeo.2.2.2.2.2.2,←normValue_mul]
    rfl
  rw [hscale]
  exact hh

theorem centered_moment_radical_payment (cost R α : ℝ) (hR : 0<R)
    (hcost : cost≤R^(-2:ℝ)) : cost*R^(2*α)≤R^(2*α-2) := by
  have h:=mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hR.le (2*α))
  rw [←Real.rpow_add hR] at h
  convert h using 1 <;> congr 1 <;> ring

/-- Both allocation-cardinality losses are paid before the radical sum.
The common norm product is bounded by the fourth radical power only when
the actual two column valuations have been bounded by two. -/
theorem allocation_radical_payment (R N A α η : ℝ)
    (hR : 1≤R) (hN : 0≤N) (hA : 0≤A) (hη : 0≤η)
    (hNcap : N≤R^4) (hmargin : 2*α+4*η≤1) :
    (A*N^η)*R^(2*α-2)≤A/R := by
  have hRp : 0<R:=zero_lt_one.trans_le hR
  have hp:=Real.rpow_le_rpow hN hNcap hη
  have he : (R^4)^η=R^(4*η) := by
    rw [←Real.rpow_natCast R 4,←Real.rpow_mul hRp.le]
    norm_num
  rw [he] at hp
  have h:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA)
    (Real.rpow_nonneg hRp.le (2*α-2))
  calc
    _≤A*R^(4*η)*R^(2*α-2):=h
    _=A*R^(2*α+4*η-2):=by rw [mul_assoc,←Real.rpow_add hRp];congr 1;congr 1;ring
    _≤A*R^(-1:ℝ):=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hA
    _=A/R:=by rw [Real.rpow_neg_one];rfl

theorem selected_allocation_margin : 2*(499/1000:ℝ)+4*(1/10000:ℝ)≤1 := by norm_num

end
end OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.radial_scalar_bound
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_retained_radical_cost
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.centered_moment_radical_payment
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.allocation_radical_payment
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.selected_allocation_margin
