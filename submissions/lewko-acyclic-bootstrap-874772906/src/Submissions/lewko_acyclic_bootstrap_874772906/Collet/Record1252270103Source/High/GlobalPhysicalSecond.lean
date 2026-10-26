/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual normalized modified MAIN Gauss energy enters the second transform
with the complete original zero filter and explicit zero/tail terms. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalAllocationMain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.CoupledRetained
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSecondTail CenteredMomentSupportedTailAggregate Record1252270103Second
local notation "O" => ActualEisensteinCubic.O

lemma gaussEnergy_scalar {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (k : ℂ) (W : 𝓢(ℝ,ℂ)) (H : ℝ) :
    gaussEnergy S a ha (fun i=>k*c i) W H=(‖k‖^2:ℝ)*gaussEnergy S a ha c W H := by
  have hp (z:O) : gaussPolynomial S a ha (fun i=>k*c i) z=k*gaussPolynomial S a ha c z := by
    unfold gaussPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold gaussEnergy
  simp_rw [hp,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc]
  exact tsum_mul_left

theorem normalized_source_gauss (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (H : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>β I*((Real.sqrt T:ℂ)⁻¹*rowWeight η fixedBadMask 1 1 t I)) W H=
      (T:ℂ)⁻¹*sourceGaussEnergy S β (heightCoeff η t) W H := by
  have hc : (fun I:supportedColumns S=>β I*((Real.sqrt T:ℂ)⁻¹*rowWeight η fixedBadMask 1 1 t I))=
      (fun I:supportedColumns S=>(Real.sqrt T:ℂ)⁻¹*(β I*heightCoeff η t I)) := by
    funext I
    rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp I.property).2]
    ring
  rw [hc,gaussEnergy_scalar]
  have hn : ‖(Real.sqrt T:ℂ)⁻¹‖^2=T⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow,Real.sq_sqrt hT.le]
  rw [hn,Complex.ofReal_inv]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- This is an equality for the actual modified coefficient, before any
ordinary/exceptional second-row split or analytic child estimate. -/
theorem actual_normalized_second_transform (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : ℝ) (hH : 0<H) :
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=CoupledFirst.coefficient s modifier R seed
    gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>β I*((Real.sqrt T:ℂ)⁻¹*rowWeight s.η fixedBadMask 1 1 s.t I)) W H=
      (T:ℂ)⁻¹*(((H:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t+
        (∑q∈(Finset.univ:Finset (BlockIndex s modifier R seed H Tsec Z ξ)).filter
          (fun q=>Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q≠0),
          blockWeight s modifier R seed H Tsec Z ξ q*
            Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q)+
        secondDiscardedEnergy s.η s.t S β W H Tsec Z ξ) := by
  dsimp only
  rw [normalized_source_gauss _ _ s.η s.t T hT W H,
    sourceGaussEnergy_localized s.η s.t _ _ W H Tsec Z ξ hH,
    actual_retained_original_nonzero s modifier R seed hz₁ hz₂ W H Tsec Z ξ hH]

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.gaussEnergy_scalar
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_source_gauss
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_normalized_second_transform
