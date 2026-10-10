import WeightedQRH.NumeratorReflectionData
import WeightedQRH.NumeratorRetainedFixed
import WeightedQRH.NumeratorDiscarded

/-! Certified selected fourth moments of the original physical numerator.
The reflection data exist by a proved theorem and preserve the actual row
coefficients. Coefficient choices, scales and primitive presentations may vary
independently with each row; no new analytic estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open WeightedNumeratorReflection CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

theorem certified_original_numerator_fourth {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ)
    (hloss : 0<loss) (hxi : 0<xi) (hb : 0<b) (hCslot : 0<Cslot) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(data : ∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : rows→ℝ)(Y m : ℝ),
      0<Y → (∀i,0<N i ∧ N i ≤ b*Y) → 0 ≤ m → m+xi ≤ 2 →
      (∀i,(data i).combinedConductor ≤ (fixedConductorConstant F.S:ℝ)*U^m*(Y/N i)) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 ≤ width i) →
      (∀i,width i ≤ CenteredMomentEnergyWidthRanges.fineMesh 2 0 1 (3/4) (D.t/4)) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (2*(m+xi)+6*(3/4)*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ Cslot*U^q) →
      (∑i:rows,‖HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0‖^4*
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0<Ccond := by dsimp [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  obtain ⟨degree,Cr,hCr,hret⟩ := certified_retained_fixed_profile F hbeta G loss Ccond Ccond xi
    hloss hCcond hCcond hxi
  obtain ⟨Ct,hCt,htail⟩ := subtype_discarded_fourth_negligible (xi/2) 0 q b Ccond Cslot
    (by positivity) hb hCcond hCslot G
  refine ⟨degree,8*(Cr+Ct),by positivity,?_⟩
  filter_upwards [hret] with U hret
  have hU := hret.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N Y m hY hN hm hmmax hcombined T width z height hw hwmax hz hheight hzim hcap hQ
  let τ (i:rows) := (data i).presentation
  let ψ (i:rows) := (data i).primitive
  let R (i:rows) := retainedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let tail (i:rows) := discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let Q (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let P (i:rows) := HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
  have hc (i:rows) : (data i).combinedConductor ≤ Ccond*U :=
    (data i).combined_le_row.trans (mul_le_mul_of_nonneg_left (hrows i.val i.property).2 hCcond.le)
  have hred (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U :=
    (data i).redundant_le_combined.trans (hc i)
  have hr := hret.2 rows hrows τ ψ (fun i=>Y/N i) m (fun i=>(data i).element_eq)
    (fun i=>div_pos hY (hN i).1) hm hmmax hred hcombined T width z height
    hw hwmax hz hheight hzim hcap
  have ht := htail rows τ ψ N Q Y U hY hU.le hN (fun u hu=>(hrows u hu).2) hc hQ
  simp only [show (xi/2)/2=xi/4 by ring,neg_zero,Real.rpow_zero,mul_one] at ht
  have hsplit (i:rows) : P i=(data i).phase*(R i+tail i) :=
    (data i).split G (Y/N i) (U^(xi/4)) (div_pos hY (hN i).1)
  have hh := original_split_weighted_fourth Finset.univ P R tail (fun i=>(data i).phase) Q
    (fun _=>1) (Cr*(1+height)^degree*U^(1+D.t+loss)) Ct
    (fun _ _=>le_rfl) (fun i _=>(data i).phase_norm) (fun i _=>hsplit i)
    (by simpa only [Complex.ofReal_one,div_one] using hr) ht
  simp only [Complex.ofReal_one,div_one] at hh
  have hH : 1 ≤ (1+height)^degree := one_le_pow₀ (by linarith)
  have hpow : 1 ≤ U^(1+D.t+loss) := Real.one_le_rpow hU.le (by linarith [D.t_pos])
  have hcost : 1 ≤ (1+height)^degree*U^(1+D.t+loss) := one_le_mul_of_one_le_of_one_le hH hpow
  have hCt' := mul_le_mul_of_nonneg_left hcost hCt.le
  exact hh.trans (by nlinarith)

end WeightedQRH.Numerator
end
