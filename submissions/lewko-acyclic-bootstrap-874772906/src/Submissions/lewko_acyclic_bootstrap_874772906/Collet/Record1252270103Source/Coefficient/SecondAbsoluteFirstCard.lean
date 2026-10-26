/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual injectively selected first labels have a polynomial cardinality.
The existing arithmetic label/projector count supplies the count; no analytic
energy estimate or count of the original unselected row family is used. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainRemainderCount
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
local notation "O"=>HeckeFamily.O

theorem eventually_selected_first_card (B L:ℝ) (hB:0≤B) (hL:0≤L) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι]
      (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K ξ:ℝ)(hK:0<K)
      (bin:ℤ×(Fin 5→ℤ)),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
    ∀(J:Type*)[Fintype J]
      (column:J→FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column j),
        (column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^L)→
      (Fintype.card J:ℝ)≤C*Z^(B+L+1) := by
  obtain ⟨C,hC,hcount⟩:=MarkedMainRemainder.eventual_selected_modified_payment B L (1/2)
    hB hL (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι instDec s modifier R seed K ξ hK bin hs hs0 hz₁ hz₂ hsource
    J instJ column hinj hlive hcap
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hcost (j:J) : (1:ℝ)≤Z^((B+L)-geometryExponents s modifier R seed K Z ξ (column j).1.val 2)/
      ((column j).2.1.val.absNorm:ℝ) := by
    have hn:=actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource
      (column j).1.val 2
    have he:geometryExponents s modifier R seed K Z ξ (column j).1.val 2≤B := by
      have hlog:=Real.logb_le_logb_of_le hZ.1 (zero_lt_one.trans_le hn.1) hn.2
      rw [Real.logb_rpow hz hZ.1.ne'] at hlog
      exact hlog
    have hp:0<((column j).2.1.val.absNorm:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (actual_first_divisor_ne_zero (geometryFirstSource s modifier R seed K Z ξ hK bin (column j).1)
          (column j).2.1))
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (hcap j).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hh:=hZ.2 s modifier R seed K ξ hK bin hs hs0 hz₁ hz₂ hsource
    J column hinj hlive hcap 1 (B+L) (fun _=>1) (by norm_num)
    (fun j=>by simpa only [one_mul] using hcost j)
  have hseednorm:(1:ℝ)≤seed.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hc:(Fintype.card J:ℝ)≤C*Z^(B+L+1)/(seed.absNorm:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      show (2:ℝ)*(1/2)=1 by norm_num] using hh
  exact hc.trans (div_le_self (mul_nonneg hC.le (Real.rpow_nonneg hz.le _)) hseednorm)

end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.eventually_selected_first_card
