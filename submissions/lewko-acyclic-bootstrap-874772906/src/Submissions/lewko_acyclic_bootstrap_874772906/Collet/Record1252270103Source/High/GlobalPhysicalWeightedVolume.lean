/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual effective second phase has a polynomial weighted-volume bound.
The original parent normalizer is preserved. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSectorWeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentCanonicalFirst CenteredMomentSupport CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentSourceRow CenteredMomentSecondPhysicalLedger
open Cycle61InitialMass Record1252270103Second
local notation "O"=>HeckeFamily.O

theorem actual_normalizer_norm_cap (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (heq:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D)):
    normalizer C D U≤(C.absNorm:ℝ) := by
  have hd:Ideal.span {commonFrequencyGenerator C D}∣C:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD heq).1
    simpa only [primary_span_supported C hC] using hh
  have hn:=divisor_norm_le _ C hC.1 hd
  have hp:=common_product_pos C D hC U
  have hone:1≤((∏p∈U,p.val).absNorm:ℝ):=by
    exact_mod_cast (show 1≤(∏p∈U,p.val).absNorm from by exact_mod_cast hp)
  rw [normalizer,actual_partitionNormalizer C D hC U]
  exact (div_le_self (Nat.cast_nonneg _) hone).trans hn

/-- No row count is hidden in this pointwise phase bound. It is uniform in
both Mellin variables and also in zero selected blocks. -/
theorem effective_weighted_volume_cap {α Label:Type*}[Fintype α][DecidableEq α]
    (N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
    (w:Label→ℂ)(W:𝓢(ℝ,ℂ))(hN:Fintype.card α≤N)
    (hlower:∀l,lo≤(d l).input.lower)
    (hW₁:∀l x,(d l).input.W₁ x≠0→ap≤x)(hW₂:∀l x,(d l).input.W₂ x≠0→ap≤x)
    (a T:Label→ℝ)(hT:∀l,0<T l)(ha:∀l,0≤a l)(hw:∀l,‖w l‖≤a l/T l)
    (Z Ca Ba BT BH BC BV:ℝ)(hZ:1<Z)(hCa:0≤Ca)
    (haCap:∀l,a l≤Ca*Z^Ba)(hTcap:∀l,Z^(-BT)≤T l)
    (hHcap:∀l,(d l).K≤Z^BH)(hCcap:∀l,((d l).C.absNorm:ℝ)≤Z^BC)
    (hVcap:∀l,volume (d l).input.toData≤Z^BV)(l:Label):
    ‖secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W l‖*
      (d l).block.outside*(volume (d l).input.toData)^2≤
        (Ca/lowerFactor N lo ap)*Z^(Ba+BT+BH+BC+BV) := by
  have hh : ‖secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W l‖*
      (d l).block.outside*volume (d l).input.toData≤
      (a l/T l)*((d l).K/lowerFactor N lo ap)*normalizer (d l).C (d l).D (d l).inactive := by
    have hp:=lowerFactor_pos N lo ap hlo hap
    have hv:=volume_pos (d l).input.toData
    have hn:=normalizer_pos (d l).C (d l).D (d l).hC (d l).inactive
    by_cases h:(modifiedDatumBlock (d l) (modifier l)).value W=0
    · simp only [secondEffectiveWeight,h,ite_true,norm_zero,zero_mul]
      exact mul_nonneg (mul_nonneg (div_nonneg (ha l) (hT l).le)
        (div_pos (d l).K_pos hp).le) hn.le
    · have ho:=actual_modified_second_outside N lo ap hlo hap (d l) (modifier l) W hN
        (hlower l) (hW₁ l) (hW₂ l) h
      simp only [secondEffectiveWeight,h,ite_false]
      have hm:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ho (norm_nonneg (w l))) hv.le
      calc
        _ ≤ ‖w l‖*((d l).K/lowerFactor N lo ap)*normalizer (d l).C (d l).D (d l).inactive := by
          convert hm using 1 <;> field_simp <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hw l) (div_pos (d l).K_pos hp).le) hn.le
  have hv:0<volume (d l).input.toData:=volume_pos _
  have hn:=actual_normalizer_norm_cap (d l).C (d l).D (d l).hC (d l).hD (d l).sameSupport (d l).inactive
  have hlof:=lowerFactor_pos N lo ap hlo hap
  have hz:=zero_lt_one.trans hZ
  have hit:(T l)⁻¹≤Z^BT:=by
    have hi:=inv_le_inv₀ (hT l) (Real.rpow_pos_of_pos hz (-BT)) |>.mpr (hTcap l)
    simpa only [Real.rpow_neg hz.le,inv_inv] using hi
  have hp:=mul_le_mul_of_nonneg_right hh hv.le
  change _≤((a l/T l)*((d l).K/lowerFactor N lo ap)*normalizer (d l).C (d l).D (d l).inactive)*volume (d l).input.toData at hp
  calc
    _≤((a l/T l)*((d l).K/lowerFactor N lo ap)*normalizer (d l).C (d l).D (d l).inactive)*volume (d l).input.toData:=by
      convert hp using 1 <;> ring
    _≤((Ca*Z^Ba*Z^BT)*(Z^BH/lowerFactor N lo ap)*Z^BC)*Z^BV:=by
      rw [div_eq_mul_inv (a l)]
      have hnn := (normalizer_pos (d l).C (d l).D (d l).hC (d l).inactive).le
      have hkn := (div_pos (d l).K_pos hlof).le
      have htn := (inv_pos.mpr (hT l)).le
      gcongr
      · exact haCap l
      · exact hHcap l
      · exact hn.trans (hCcap l)
      · exact hVcap l
    _=_:=by simp only [Real.rpow_add hz];ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_normalizer_norm_cap
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.effective_weighted_volume_cap
