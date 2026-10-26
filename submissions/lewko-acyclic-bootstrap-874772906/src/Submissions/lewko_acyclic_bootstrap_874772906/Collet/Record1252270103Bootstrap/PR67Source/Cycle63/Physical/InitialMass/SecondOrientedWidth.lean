import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRowState
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondChildCaps
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonical CenteredMomentSecondRetainedWidth
open Cycle63FinalNatural
open RayFourExpansion CenteredMomentSecondRadicalBudget

theorem main_inverse_radius_log_oriented (reflected : Bool) (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kmain := mainCommonRadius Z d K0 c (3*a) δ reserve
    Real.logb Z (frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ)+
      Real.logb Z (τ.modulus.absNorm:ℝ) =
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve+
        Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hr := main_fourier_frequency_log reflected C D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
    hC.1 hD.1 (subsetGenerator_supported C D hC E).1 heq
    K V Z (3*a) δ reserve ξ b N hK hV hZ hb
  have hw := CenteredMomentFirstMixedNormalizationActual.actual_reference_width
    η τ C D hC E K Z hK hZ hmod
  dsimp only at hr
  linarith

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem actual_second_live_main_width_oriented (reflected : Bool) (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (η₀ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK₀ : 0<K₀) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : (d r.val.1).input.η.modulus=η₀.modulus*
      Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E*
        activeConductor C₁ D₁})
    (Bmask : ℝ) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let c := Real.logb Z ((if reflected then D₁ else C₁).absNorm:ℝ)
    let e := Real.logb Z ((if reflected then C₁ else D₁).absNorm:ℝ)
    let k := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E}) K₀ V Z
    let Kmain := CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z e k c (3*a) δ reserve
    (d r.val.1).radius=CenteredMomentSectorLocalization.frequencyRadius
      ((b^N*V/((if reflected then D₁ else C₁).absNorm:ℝ))^2/Kmain) Z ξ →
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-max (c-e) 0-6*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hradius
  have hw := actual_second_live_state_width d r Z Bmask hZ χ Q P hP hPN
  have hr := main_inverse_radius_log_oriented reflected η₀ (d r.val.1).input.η
    C₁ D₁ hC₁ hD₁ heq E K₀ V Z a δ reserve ξ b N hK₀ hV hZ hb hmod
  dsimp only at hw hr
  rw [hradius] at hw ⊢
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
