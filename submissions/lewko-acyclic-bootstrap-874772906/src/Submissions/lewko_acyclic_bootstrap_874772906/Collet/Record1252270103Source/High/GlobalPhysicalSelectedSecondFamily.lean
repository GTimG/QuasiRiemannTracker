/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Selected first MAIN children enter one joint second-sector family. The
complete-block zero filter and the original parent normalizer are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedSecond
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondSectorDatumFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
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
local notation "O"=>ActualEisensteinCubic.O
local instance selectedSecondFamilyDecidable {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- The two norms contain every selected first label simultaneously. The
only premises beyond the actual finite data are polynomial support bounds. -/
theorem actual_selected_second_family
    (N:ℕ)(hiMax wlo whi B Bseed ξ saving ε:ℝ)
    (hhi:0≤hiMax)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ)(hε:0<ε):
    ∃S₀ S₁:Finset (ℕ×ℕ),∃C₀ C₁:ℝ,0<C₀ ∧ 0<C₁ ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label:Type}[Fintype α][DecidableEq α][Fintype Label],Fintype.card α≤N→
    ∀(s:Input α)(A₁ A₂ D K R:Ideal O)(C seed:Label→Ideal O)
      (alloc:∀l,actualAllocations s.pools (C l))(τ:Label→Character)(t:ℝ)
      (P:Finset (Ideal O)),P.Nonempty→(∀p∈P,Prime p)→
    let slots:=fun l=>liveIndices (alloc l).val
    let schild:=fun l=>child s (C l) R (alloc l) (τ l) t
    let modifier:=fun l=>correctedModifier P (A₁*(alloc l).val (Sum.inr 0))
      (A₂*(alloc l).val (Sum.inr 1)) (D*C l) (K*markedProduct (alloc l).val) (fun _=>1)
    ∀ell Bcap:ℝ,0<ell→(∀p∈P,Z^ell≤(p.absNorm:ℝ))→
    2*(Bcap/ell)≤(P.card:ℝ)→(∀l,sourceRadius (schild l)≤Z^Bcap)→
    ∀W₁ W₂:𝓢(ℝ,ℂ),s.W₁=W₁→s.W₂=W₂→
    ∀(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0),
    Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
    Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hiMax)→
    ∀hseed:∀l,Squarefree (seed l),
    (∀l,(seed l).absNorm≤Z^Bseed)→
    ∀(Λ H Tsec:Label→ℝ)(T:ℝ),
    (∀l,0<Λ l)→0<T→(∀l,sourceRadius (schild l)≤Λ l*T)→
    ∀hH:∀l,0<H l,
    (∀l,volume (schild l).toData≤Z^B)→(∀l,Tsec l≤Z^B)→
    (∀l,(volume (schild l).toData)^2/H l≤Tsec l)→
    ∀a:Label→ℝ,(∀l,0≤a l)→
    ∀keep:∀l,BlockIndex (schild l) (modifier l) (R*C l) (seed l) (H l) (Tsec l) Z ξ→O→Prop,
    let zeroTerm:=fun l=>C₀*(4*plainControl (schild l) W₁ W₂)^2*
      S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*H l*(Λ l)^(1+ε)*T^ε/(seed l).absNorm
    let tailTerm:=fun l=>C₁*(2*plainControl (schild l) W₁ W₂)^2*
      S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*H l*
        (volume (schild l).toData/T)*Z^(-saving)/(seed l).absNorm
    let family:=CompleteFamily slots schild modifier (fun l=>R*C l) seed ballProfile H Tsec (fun _=>Z) (fun _=>ξ)
    (∑l,a l*correctedChildGaussEnergy s A₁ A₂ D K (C l) R (seed l) (fun _=>1) P
      (alloc l) (τ l) t T (H l))≤
      (∑l,a l*zeroTerm l)+
      (‖∑q:family,familyWeight slots schild modifier (fun l=>R*C l) seed ballProfile H Tsec
        (fun _=>Z) (fun _=>ξ) (fun _=>T) a keep q*
        (modifiedDatumBlock (familyDatum slots schild modifier (fun l=>R*C l) seed hseed
          (fun _=>hz₁) (fun _=>hz₂) ballProfile H Tsec (fun _=>Z) (fun _=>ξ)
          hH keep q) (modifier q.1)).value ballProfile‖+
       ‖∑q:family,familyWeight slots schild modifier (fun l=>R*C l) seed ballProfile H Tsec
        (fun _=>Z) (fun _=>ξ) (fun _=>T) a (fun l q z=>¬keep l q z) q*
        (modifiedDatumBlock (familyDatum slots schild modifier (fun l=>R*C l) seed hseed
          (fun _=>hz₁) (fun _=>hz₂) ballProfile H Tsec (fun _=>Z) (fun _=>ξ)
          hH (fun l q z=>¬keep l q z) q) (modifier q.1)).value ballProfile‖)+
      ∑l,a l*tailTerm l := by
  obtain ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,hsource⟩:=actual_selected_child_second_reduction
    N hiMax wlo whi B Bseed ξ saving ε hhi hwlo hwhi hB hξ hε
  refine ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label _ _ _ hcard s A₁ A₂ D K R C seed alloc τ t P hP hp slots schild modifier
    ell Bcap hell hlower hsize hsource W₁ W₂ he₁ he₂ hz₁ hz₂ hs₁ hs₂ hshi hseed hseedcap
    Λ H Tsec T hΛ hT hsourceT hH hV hTsec hnom a ha keep zeroTerm tailTerm family
  have hpoint (l:Label):=
    hZ.2 hcard s A₁ A₂ D K (C l) R (seed l) (alloc l) (τ l) t P hP hp ell Bcap
      hell hlower hsize (hsource l) W₁ W₂ he₁ he₂ hz₁ hz₂ hs₁ hs₂ hshi
      (hseed l).ne_zero (hseedcap l) (Λ l) T (hΛ l) hT (hsourceT l)
      (H l) (Tsec l) (hH l) (hV l) (hTsec l) (hnom l) (keep l)
  have hsum:=Finset.sum_le_sum (fun l (_:l∈(Finset.univ:Finset Label))=>
    mul_le_mul_of_nonneg_left (hpoint l) (ha l))
  change _≤∑l,a l*(zeroTerm l+
    secondSectorMass (schild l) (modifier l) (R*C l) (seed l) ballProfile (H l) (Tsec l) Z ξ T (keep l)+
      tailTerm l) at hsum
  simp_rw [mul_add] at hsum
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
  rw [second_sector_family_phase slots schild modifier (fun l=>R*C l) seed hseed
    (fun _=>hz₁) (fun _=>hz₂) ballProfile H Tsec (fun _=>Z) (fun _=>ξ) (fun _=>T) a
    hH (fun _=>hT) ha keep] at hsum
  exact hsum

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_selected_second_family
