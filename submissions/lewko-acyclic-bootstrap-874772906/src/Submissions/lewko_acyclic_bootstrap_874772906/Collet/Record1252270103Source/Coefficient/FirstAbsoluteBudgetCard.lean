/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The full first live-column set has polynomial cardinality. Actual dyad/ray
multiplicities are retained through the checked finite cost selection. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondAbsoluteFirstCard
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstAllocationSelectionColumns
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstAbsoluteBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.Admission.FirstAllocationSelection
local notation "O"=>HeckeFamily.O
local instance firstAbsoluteBudgetCardDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem eventually_full_first_card (A D B L ξ:ℝ)
    (hA:0≤A)(hD:0≤D)(hB:0≤B)(hL:0≤L)(hξ:0≤ξ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι]
      (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(K:ℝ)(hK:0<K)
      (bin:ℤ×(Fin 5→ℤ)),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      0<sourceRadius s→sourceRadius s≤Z^B→volume s≤Z^A→K⁻¹≤Z^D→
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^L)→
      ((firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK bin)
        (fun _=>logAnnulus)).card:ℝ)≤C*Z^(B+L+2) := by
  obtain ⟨C₀,hC₀,hselect⟩:=actual_first_full_cost_selection A D B ξ 1 hA hD hB hξ (by norm_num)
  obtain ⟨C₁,hC₁,hcard⟩:=SecondAbsoluteEnvelope.eventually_selected_first_card B L hB hL
  refine ⟨C₀*C₁,mul_pos hC₀ hC₁,?_⟩
  filter_upwards [hselect,hcard] with Z hselect hcard
  refine ⟨hcard.1,?_⟩
  intro ι instι instDec s modifier R seed K hK bin hs hs0 hz₁ hz₂ hpos hsource hvolume hKi hpool
  let src:=geometryFirstSource s modifier R seed K Z ξ hK bin
  let live:=firstLiveColumns src (fun _=>logAnnulus)
  let arith:=fun j:live=>columnKey s modifier R seed K Z ξ hK bin j.val
  obtain ⟨pick,hkey,hinj,hcost⟩:=hselect.2 s modifier R seed K hK bin hs hz₁ hz₂
    hpos hsource hvolume hKi live (fun _=>1) (fun _=>by norm_num)
  have hc:((Finset.univ.image arith).card:ℝ)≤C₁*Z^(B+L+1) := by
    have hh:=hcard.2 s modifier R seed K ξ hK bin hs hs0 hz₁ hz₂ hsource
      (Finset.univ.image arith) (fun j=>(pick j).val) hinj (fun j=>(pick j).property)
      (fun j=>(first_divisor_norm (src (pick j).val.1) (Z^L)
        (by
          intro I hI
          apply hpool I
          obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hI
          exact Finset.mem_image.mpr ⟨v,Fintype.mem_piFinset.mpr (Fintype.mem_piFinset.mp hv),rfl⟩)
        (pick j).val.2.1).2)
    simpa only [Fintype.card_coe] using hh
  have hcost':(live.card:ℝ)≤(C₀*Z)*((Finset.univ.image arith).card:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,Real.rpow_one] using hcost
  have hz:0<Z:=zero_lt_one.trans hcard.1
  have hpow:Z*Z^(B+L+1)=Z^(B+L+2) := by
    calc
      _=Z^(1:ℝ)*Z^(B+L+1) := by rw [Real.rpow_one]
      _=_ := by rw [←Real.rpow_add hz];congr 1;ring
  exact hcost'.trans ((mul_le_mul_of_nonneg_left hc (mul_nonneg hC₀.le hz.le)).trans_eq (by
    calc
      _=(C₀*C₁)*(Z*Z^(B+L+1)) := by ring
      _=_ := by rw [hpow]))

end
end QRH.Record1252270103Source.FirstAbsoluteBudget
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.eventually_full_first_card
