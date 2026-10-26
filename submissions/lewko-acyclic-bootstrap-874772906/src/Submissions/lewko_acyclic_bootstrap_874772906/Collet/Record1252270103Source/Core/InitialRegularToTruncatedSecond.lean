/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The selected corrected MAIN children enter the actual two full sector norms.
The correction is evaluated at the child column, and both profiles are literal. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedSecondFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedContract

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
open OAI.SevenEighths.Record1252270103Source.Collision
open Record1252270103Second SecondRemainder SecondSectorDatum
open High.CoupledFirst High.GlobalPhysical Low.SelectedExceptionalNormalized
open Low.SelectedExceptionalInitialCaps Admission.SelectedSecondNatural RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance initialSecondJointDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem eventual_selected_second (N:ℕ)(B ξ saving ε:ℝ)
    (hB:0≤B)(hξ:0<ξ)(hε:0<ε):
    ∃S₀ S₁:Finset (ℕ×ℕ),∃C₀ C₁:ℝ,0<C₀ ∧ 0<C₁ ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label:Type}[Fintype α][DecidableEq α][Fintype Label],Fintype.card α≤N→
    ∀(s:Input α)(R:Ideal O)(C seed:Label→Ideal O)
      (alloc:∀l,actualAllocations s.pools (C l))(τ:Label→Character)(t:ℝ)
      (P:Finset (Ideal O)),P.Nonempty→(∀p∈P,Prime p)→
    ∀ell Bcap:ℝ,0<ell→(∀p∈P,Z^ell≤(p.absNorm:ℝ))→
    2*(Bcap/ell)≤(P.card:ℝ)→
    (∀l,sourceRadius (child s (C l) R (alloc l) (τ l) t)≤Z^Bcap)→
    ∀W₁ W₂:𝓢(ℝ,ℂ),s.W₁=W₁→s.W₂=W₂→
    ∀(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0),
    Function.support (W₁:ℝ→ℂ)⊆Set.Icc (1/4:ℝ) (9/4)→
    Function.support (W₂:ℝ→ℂ)⊆Set.Icc (1/4:ℝ) (9/4)→(∀i,s.hi i≤2)→
    ∀hseed:∀l,Squarefree (seed l),(∀l,((seed l).absNorm:ℝ)≤Z^(4:ℝ))→
    ∀(Λ H Tsec:Label→ℝ)(T:ℝ),
    (∀l,0<Λ l)→0<T→(∀l,sourceRadius (child s (C l) R (alloc l) (τ l) t)≤Λ l*T)→
    ∀hH:∀l,0<H l,
    (∀l,volume (child s (C l) R (alloc l) (τ l) t)≤Z^B)→
    (∀l,Tsec l≤Z^B)→
    (∀l,(volume (child s (C l) R (alloc l) (τ l) t))^2/H l≤Tsec l)→
    ∀(amplitude:Label→ℝ),(∀l,0≤amplitude l)→
    ∀(χ₀:Label→RayCharacter)(m:O)(Q:Ideal O),
    let f:=mainAllocatedFamily s ballProfile W₁ W₂ Z R C seed alloc τ (fun _=>t) P hseed
      hz₁ hz₂ H Tsec (fun _=>T) amplitude ξ hH χ₀ m
    let zeroTerm:=fun l=>C₀*(4*plainControl (f.input l) W₁ W₂)^2*
      S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*H l*(Λ l)^(1+ε)*T^ε/(seed l).absNorm
    let tailTerm:=fun l=>C₁*(2*plainControl (f.input l) W₁ W₂)^2*
      S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*H l*
        (volume (f.input l)/T)*Z^(-saving)/(seed l).absNorm
    (∑l,amplitude l*correctedChildGaussEnergy s 1 1 1 1 (C l) R (seed l) (fun _=>1) P
      (alloc l) (τ l) t T (H l))≤
      (∑l,amplitude l*zeroTerm l)+
      (regularJointNorm f Q+‖∑q:f.Carrier,f.phase Q q*(f.block Q q).value ballProfile‖)+
      ∑l,amplitude l*tailTerm l := by
  obtain ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,hbound⟩:=actual_selected_second_family
    N 2 (1/4) (9/4) B 4 ξ saving ε (by norm_num) (by norm_num) (by norm_num) hB hξ hε
  refine ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,hbound.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro α Label _ _ _ hN s R C seed alloc τ t P hP hp ell Bcap hell hlower hsize hsource
    W₁ W₂ he₁ he₂ hz₁ hz₂ hs₁ hs₂ hhi hseed hseedcap Λ H Tsec T hΛ hT hsourceT hH
    hV hTsec hnom amplitude ha χ₀ m Q f zeroTerm tailTerm
  have hh:=hz.2 hN s 1 1 1 1 R C seed alloc τ t P hP hp ell Bcap hell hlower hsize hsource
    W₁ W₂ he₁ he₂ hz₁ hz₂ hs₁ hs₂ hhi hseed hseedcap Λ H Tsec T hΛ hT hsourceT hH
    hV hTsec hnom amplitude ha
    (regularKeep (fun l=>liveIndices (alloc l).val)
      (fun l=>child s (C l) R (alloc l) (τ l) t)
      (fun l=>correctedModifier P (1*(alloc l).val (Sum.inr 0))
        (1*(alloc l).val (Sum.inr 1)) (1*C l) (1*markedProduct (alloc l).val) (fun _=>1))
      (fun l=>R*C l) seed H Tsec Z ξ χ₀ Q m)
  have hm : (fun l=>correctedModifier P (1*(alloc l).val (Sum.inr 0))
      (1*(alloc l).val (Sum.inr 1)) (1*C l) (1*markedProduct (alloc l).val) (fun _=>1))=
      f.modifier := by
    funext l
    simp only [f,mainAllocatedFamily,allocatedFamily,CorrectedFamilyData.modifier,
      correctedModifier,one_mul,mul_one]
    congr 1
    funext I
    simp [poolCorrection]
  let joint (g:∀l,Tuple (liveIndices (alloc l).val)→ℂ):ℝ :=
    let keep:=regularKeep (fun l=>liveIndices (alloc l).val) (fun l=>child s (C l) R (alloc l) (τ l) t)
      g (fun l=>R*C l) seed H Tsec Z ξ χ₀ Q m
    let family:=CompleteFamily (fun l=>liveIndices (alloc l).val)
      (fun l=>child s (C l) R (alloc l) (τ l) t) g (fun l=>R*C l) seed ballProfile H Tsec
      (fun _=>Z) (fun _=>ξ)
    ‖∑q:family,familyWeight (fun l=>liveIndices (alloc l).val)
      (fun l=>child s (C l) R (alloc l) (τ l) t) g (fun l=>R*C l) seed ballProfile H Tsec
      (fun _=>Z) (fun _=>ξ) (fun _=>T) amplitude keep q*
      (modifiedDatumBlock (familyDatum (fun l=>liveIndices (alloc l).val)
        (fun l=>child s (C l) R (alloc l) (τ l) t) g (fun l=>R*C l) seed hseed
        (fun _=>hz₁) (fun _=>hz₂) ballProfile H Tsec (fun _=>Z) (fun _=>ξ) hH keep q)
        (g q.1)).value ballProfile‖+
    ‖∑q:family,familyWeight (fun l=>liveIndices (alloc l).val)
      (fun l=>child s (C l) R (alloc l) (τ l) t) g (fun l=>R*C l) seed ballProfile H Tsec
      (fun _=>Z) (fun _=>ξ) (fun _=>T) amplitude (fun l q z=>¬keep l q z) q*
      (modifiedDatumBlock (familyDatum (fun l=>liveIndices (alloc l).val)
        (fun l=>child s (C l) R (alloc l) (τ l) t) g (fun l=>R*C l) seed hseed
        (fun _=>hz₁) (fun _=>hz₂) ballProfile H Tsec (fun _=>Z) (fun _=>ξ) hH
        (fun l q z=>¬keep l q z) q) (g q.1)).value ballProfile‖
  change _≤(∑l,amplitude l*zeroTerm l)+joint
    (fun l=>correctedModifier P (1*(alloc l).val (Sum.inr 0))
      (1*(alloc l).val (Sum.inr 1)) (1*C l) (1*markedProduct (alloc l).val) (fun _=>1))+
    ∑l,amplitude l*tailTerm l at hh
  change _≤(∑l,amplitude l*zeroTerm l)+joint f.modifier+∑l,amplitude l*tailTerm l
  rw [←hm]
  exact hh

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.eventual_selected_second
