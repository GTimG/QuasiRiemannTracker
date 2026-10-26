/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Polynomial caps for the literal first scalar, allocation count and row bands.
The bounds depend only on genuine source geometry and retain character zeros. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalMassAbsolute
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.MarkedMainRemainderAllocation
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstAllocationSelectionColumns
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstAbsoluteBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentDyadicCount CenteredMomentSectorLocalization
open CenteredMomentFirstAnnularMajorant CenteredMomentExceptionalAmplitudePair
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O

theorem canonical_scalar_sq {ι:Type}[Fintype ι][DecidableEq ι]
    (reflected:Bool)(N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (M Z ξ B:ℝ)(hZ:1<Z)(hK:0<Z^M)(hB:0≤B)
    (hcard:Fintype.card ι≤N)(hlower:lo≤s.lower)(hs:Squarefree seed)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(hsource:sourceRadius s≤Z^B)
    (hs₁:∀x,s.W₁ x≠0→ap≤x)(hs₂:∀x,s.W₂ x≠0→ap≤x)
    (hA:|Real.logb Z (volume s)|≤B)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (geometryFirstSource s modifier R seed (Z^M) Z ξ hK bin)) :
    ‖balancedColumnScalar reflected s modifier R seed (Z^M) Z ξ M (Real.logb Z (volume s))
      hK bin (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^M) Z ξ q)) j‖^2≤
      2*((geometrySupportConstant N lo ap ap)^2+1)*Z^(7*B) := by
  have h:=actual_modified_mass_coarse reflected N lo ap hlo hap s modifier R seed W
    M Z ξ B 1 hZ hK hB (by norm_num) hcard hlower hs hz₁ hz₂ hsource hs₁ hs₂ hA bin j
  simpa only [balancedFirstHighMass,sub_self,Real.rpow_zero,mul_one,
    CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume,
    show B+6*B=7*B by ring] using h

theorem allocation_card_cap (N:ℕ) :
    ∃D₀:ℝ,0<D₀ ∧ ∀{ι:Type*}[Fintype ι]
      (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K Z ξ B:ℝ)(hK:0<K),
      Fintype.card ι≤N→Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      ∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
        (j:FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK bin)),
      ((actualAllocations s.pools (geometryColumnIdeal reflected s modifier R seed K Z ξ hK bin j)).card:ℝ)^2
        ≤D₀*Z^B := by
  obtain ⟨D₀,hD₀,hbound⟩:=MarkedMainRemainder.uniform_allocation_card_square N 1 (by norm_num)
  refine ⟨D₀,hD₀,?_⟩
  intro ι inst s modifier R seed K Z ξ B hK hN hs hz₁ hz₂ hsource reflected bin j
  let C:=geometryColumnIdeal reflected s modifier R seed K Z ξ hK bin j
  have hC:C≠0 := by
    cases reflected
    · exact (geometryFirstSource s modifier R seed K Z ξ hK bin j.1).hC.1
    · exact (geometryFirstSource s modifier R seed K Z ξ hK bin j.1).hD.1
  have hn:(C.absNorm:ℝ)≤Z^B := by
    cases reflected
    · exact (actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 0).2
    · exact (actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 1).2
  have hc:=hbound s hN C hC
  rw [Real.rpow_one] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hn hD₀.le)

theorem actual_band_scale {ι:Type*}[Fintype ι]
    (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K Z ξ A D B:ℝ)
    (hK:0<K)(hZ:1≤Z)(hB:0≤B)(hA:0≤A)(hD:0≤D)(hξ:0≤ξ)
    (hs:Squarefree seed)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hpos:0<sourceRadius s)(hsource:sourceRadius s≤Z^B)
    (hV:volume s≤Z^A)(hKi:K⁻¹≤Z^D)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK bin))
    (n:ℤ)(hn:n∈bands (geometryFirstSource s modifier R seed K Z ξ hK bin j.1).H0) :
    dyadicScale n≤32*Z^(3*max A D+ξ/2) := by
  have hp:0<Z:=zero_lt_one.trans_le hZ
  have he:=actual_dyads_in_envelope s modifier R seed K Z ξ A D B hK hZ hB hA hD hξ
    hs hz₁ hz₂ hpos hsource hV hKi j.1.val 1
  have he':(j.1.val.2.2 1).val∈indices 1 (Z^(3*max A D+ξ/2)):=by simpa using he
  have hh:=(mem_indices_iff_scale 1 _ (by norm_num) (Real.rpow_pos_of_pos hp _) _).mp he'
  have hb:=bands_scale _ (geometryFirstSource s modifier R seed K Z ξ hK bin j.1).H0_pos n hn
  have hd:(geometryFirstSource s modifier R seed K Z ξ hK bin j.1).H0≤4*Z^(3*max A D+ξ/2):=hh.2
  linarith [hb.2]

end
end QRH.Record1252270103Source.FirstAbsoluteBudget
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.canonical_scalar_sq
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.allocation_card_cap
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.actual_band_scale
