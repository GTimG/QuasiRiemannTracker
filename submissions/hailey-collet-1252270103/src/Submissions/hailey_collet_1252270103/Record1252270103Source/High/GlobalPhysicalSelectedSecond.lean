/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The corrected second transform with its zero and discarded tail paid.
The remaining finite sum is the literal physical block sum, with its
original complete-zero filter and both complementary row sectors. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondRemainder
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalAllocationMain
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Zero
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Tail
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Correction
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondTail
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open Record1252270103Second SecondRemainder
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O" => ActualEisensteinCubic.O
local instance selectedSecondSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma corrected_child_gauss_as_source {ι : Type*} [Fintype ι]
    (s : Input ι) (A₁ A₂ D K C R L : Ideal O) (P : Finset (Ideal O))
    (alloc : actualAllocations s.pools C) (τ : Character) (t T H : ℝ) :
    correctedChildGaussEnergy s A₁ A₂ D K C R L (fun _=>1) P alloc τ t T H=
      let schild:=child s C R alloc τ t
      let modifier:=correctedModifier P (A₁*alloc.val (Sum.inr 0)) (A₂*alloc.val (Sum.inr 1))
        (D*C) (K*markedProduct alloc.val) (fun _=>1)
      let S:=finiteColumns (Fintype.piFinset schild.pools)
      (gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I:supportedColumns S=>CoupledFirst.coefficient schild modifier (R*C) L I*
          ((Real.sqrt T:ℂ)⁻¹*rowWeight schild.η fixedBadMask 1 1 schild.t I)) ballProfile H).re := by
  unfold correctedChildGaussEnergy
  dsimp only [correctedModifier,child_character,child_height]
  apply congrArg Complex.re
  exact source_gauss_energy_pool_decEq (ι:=liveIndices alloc.val) _ _
    (child s C R alloc τ t).pools
    (fun I=>CoupledFirst.coefficient (child s C R alloc τ t)
      (correctedModifier P (A₁*alloc.val (Sum.inr 0)) (A₂*alloc.val (Sum.inr 1))
        (D*C) (K*markedProduct alloc.val) (fun _=>1)) (R*C) L I*
      ((Real.sqrt T:ℂ)⁻¹*rowWeight τ fixedBadMask 1 1 t I)) ballProfile H

set_option linter.constructorNameAsVariable false in
/-- The selected first MAIN child has exactly the corrected coefficient of
the second transform, including the original parent-volume normalization. -/
theorem actual_selected_child_second_reduction
    (N : ℕ) (hiMax wlo whi B Bseed ξ saving ε : ℝ)
    (hhi : 0≤hiMax) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B)
    (hξ : 0<ξ) (hε : 0<ε) :
    ∃S₀ S₁ : Finset (ℕ×ℕ),∃C₀ C₁ : ℝ,0<C₀ ∧ 0<C₁ ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type*}[Fintype ι][DecidableEq ι],Fintype.card ι≤N→
    ∀(s : Input ι)(A₁ A₂ D K C R L : Ideal O)(alloc : actualAllocations s.pools C)
      (τ : Character)(t : ℝ)(P : Finset (Ideal O)),
    P.Nonempty→(∀p∈P,Prime p)→
    let schild:=child s C R alloc τ t
    ∀ell Bcap : ℝ,0<ell→(∀p∈P,Z^ell≤(p.absNorm:ℝ))→
    2*(Bcap/ell)≤(P.card:ℝ)→sourceRadius schild≤Z^Bcap→
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),s.W₁=W₁→s.W₂=W₂→s.W₁ 0=0→s.W₂ 0=0→
    Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
    Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hiMax)→
    L≠0→(L.absNorm:ℝ)≤Z^Bseed→
    ∀Λ T : ℝ,0<Λ→0<T→sourceRadius schild≤Λ*T→
    ∀H Tsec : ℝ,0<H→
    volume schild.toData≤Z^B→Tsec≤Z^B→(volume schild.toData)^2/H≤Tsec→
    let modifier:=correctedModifier P (A₁*alloc.val (Sum.inr 0)) (A₂*alloc.val (Sum.inr 1))
      (D*C) (K*markedProduct alloc.val) (fun _=>1)
    ∀keep : BlockIndex schild modifier (R*C) L H Tsec Z ξ→O→Prop,
    correctedChildGaussEnergy s A₁ A₂ D K C R L (fun _=>1) P alloc τ t T H≤
      C₀*(4*plainControl schild W₁ W₂)^2*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
        H*Λ^(1+ε)*T^ε/(L.absNorm:ℝ)+
      secondSectorMass schild modifier (R*C) L ballProfile H Tsec Z ξ T keep+
      C₁*(2*plainControl schild W₁ W₂)^2*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
        H*(volume schild.toData/T)*Z^(-saving)/(L.absNorm:ℝ) := by
  obtain ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,hr⟩:=actual_corrected_second_reduction N hiMax wlo whi B Bseed ξ saving ε
    hhi hwlo hwhi hB hξ hε
  refine ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ hcard s A₁ A₂ D K C R L alloc τ t P hP hp schild ell Bcap hell hlower hsize hsource
    W₁ W₂ he₁ he₂ hz₁ hz₂ hs₁ hs₂ hshi hL hLcap Λ T hΛ hT hsourceT H Tsec hH hV hTsec hnom modifier keep
  have hc₀ : Fintype.card (liveIndices alloc.val)≤Fintype.card ι := by
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices alloc.val)
  have hc : Fintype.card (liveIndices alloc.val)≤N := hc₀.trans hcard
  have hh:=hZ.2 hc schild
    (A₁*alloc.val (Sum.inr 0)) (A₂*alloc.val (Sum.inr 1)) (D*C) (K*markedProduct alloc.val)
    (R*C) L P hP hp ell Bcap hell hlower hsize hsource W₁ W₂
    he₁ he₂ hz₁ hz₂ hs₁ hs₂ (fun i=>hshi i.val) hL hLcap Λ T hΛ hT hsourceT
    ballProfile H Tsec hH hV hTsec hnom keep
  rw [corrected_child_gauss_as_source]
  exact hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_selected_child_second_reduction
