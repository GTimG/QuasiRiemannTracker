/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedLowCofactor
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.JointRowFibres
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport
theorem radical_product_norm_le (R H : Ideal O) (hR : R≠0) (hH : H≠0) :
    ((∏I∈ps (R*H),I).absNorm:ℝ) ≤
      ((∏I∈ps R,I).absNorm:ℝ)*(H.absNorm:ℝ) := by
  have hr : R.radical≠0 := by
    intro he
    have hh : R≤R.radical:=Ideal.le_radical
    rw [he] at hh
    exact hR (le_bot_iff.mp hh)
  rw [primeSupport_product_radical _ (mul_ne_zero hR hH),primeSupport_product_radical _ hR]
  have hle : R.radical*H≤(R*H).radical := by
    rw [Ideal.radical_mul]
    exact le_inf Ideal.mul_le_left (Ideal.mul_le_right.trans Ideal.le_radical)
  have hd:=Ideal.absNorm_dvd_absNorm_of_le hle
  have hn:=Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hr hH))) hd
  rw [map_mul] at hn
  exact_mod_cast hn

theorem radical_product_rpow_le (R H : Ideal O) (hR : R≠0) (hH : H≠0)
    (ε : ℝ) (hε : 0≤ε) :
    ((∏I∈ps (R*H),I).absNorm:ℝ)^ε ≤
      ((∏I∈ps R,I).absNorm:ℝ)^ε*(H.absNorm:ℝ)^ε := by
  have h:=Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_product_norm_le R H hR hH) hε
  rwa [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at h

theorem weighted_missing_radical_bound (R H : Ideal O) (hR : R≠0) (hH : H≠0)
    (Z lo hi ε γ : ℝ) (hZ : 0<Z) (hε : 0≤ε) (hγ : 0≤γ)
    (hlo : Z^lo≤(H.absNorm:ℝ)) (hhi : (H.absNorm:ℝ)≤Z^hi) :
    ((∏I∈ps (R*H),I).absNorm:ℝ)^ε*(H.absNorm:ℝ)^(-γ) ≤
      ((∏I∈ps R,I).absNorm:ℝ)^ε*Z^(hi*ε-γ*lo) := by
  have hpos : 0<(H.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hH)
  have hp:=Real.rpow_le_rpow hpos.le hhi hε
  have hn:=Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hZ lo) hlo (neg_nonpos.mpr hγ)
  have he : (Z^hi)^ε*(Z^lo)^(-γ)=Z^(hi*ε-γ*lo) := by
    rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ ≤ (((∏I∈ps R,I).absNorm:ℝ)^ε*(H.absNorm:ℝ)^ε)*(H.absNorm:ℝ)^(-γ) :=
      mul_le_mul_of_nonneg_right (radical_product_rpow_le R H hR hH ε hε)
        (Real.rpow_nonneg hpos.le _)
    _ = ((∏I∈ps R,I).absNorm:ℝ)^ε*((H.absNorm:ℝ)^ε*(H.absNorm:ℝ)^(-γ)) := by ring
    _ ≤ ((∏I∈ps R,I).absNorm:ℝ)^ε*((Z^hi)^ε*(Z^lo)^(-γ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp hn (Real.rpow_nonneg hpos.le _) (by positivity))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by rw [he]
end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.radical_product_norm_le
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.radical_product_rpow_le
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.weighted_missing_radical_bound
