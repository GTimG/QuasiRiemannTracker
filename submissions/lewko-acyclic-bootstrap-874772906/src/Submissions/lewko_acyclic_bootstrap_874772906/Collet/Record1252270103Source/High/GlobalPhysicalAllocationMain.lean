/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
First common-allocation energy is bounded by actual corrected child Gauss
energies. Its only premises are literal support and amplification geometry. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalAllocation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentPrimeElements
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimePool CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

/-- Choice of finite-pool equality decision is irrelevant. This small
transport avoids unfolding a dependent child Input during kernel matching. -/
lemma source_gauss_dyadic_pool_decEq (d₁ d₂ : DecidableEq (ι⊕Fin 2))
    (pools : (ι⊕Fin 2)→Finset (Ideal O)) (β : Ideal O→ℂ) (n : ℤ) :
    (∑'z:O,dyadicWeight n (normValue z)*
      ‖gaussPolynomial Finset.univ
        (sourceGenerator (finiteColumns (@Fintype.piFinset (ι⊕Fin 2) d₁ _ (fun _=>Ideal O) pools)))
        (sourceGenerator_supported _) (fun I=>β I) z‖^2)=
    (∑'z:O,dyadicWeight n (normValue z)*
      ‖gaussPolynomial Finset.univ
        (sourceGenerator (finiteColumns (@Fintype.piFinset (ι⊕Fin 2) d₂ _ (fun _=>Ideal O) pools)))
        (sourceGenerator_supported _) (fun I=>β I) z‖^2) := by
  have hd : d₁=d₂ := Subsingleton.elim _ _
  cases hd
  rfl

lemma source_gauss_energy_pool_decEq (d₁ d₂ : DecidableEq (ι⊕Fin 2))
    (pools : (ι⊕Fin 2)→Finset (Ideal O)) (β : Ideal O→ℂ) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    gaussEnergy Finset.univ
      (sourceGenerator (finiteColumns (@Fintype.piFinset (ι⊕Fin 2) d₁ _ (fun _=>Ideal O) pools)))
      (sourceGenerator_supported _) (fun I=>β I) Φ H=
    gaussEnergy Finset.univ
      (sourceGenerator (finiteColumns (@Fintype.piFinset (ι⊕Fin 2) d₂ _ (fun _=>Ideal O) pools)))
      (sourceGenerator_supported _) (fun I=>β I) Φ H := by
  have hd : d₁=d₂ := Subsingleton.elim _ _
  cases hd
  rfl

def correctedChildGaussEnergy (s : Input ι) (A₁ A₂ D K C R L : Ideal O)
    (F : Ideal O→ℂ) (P : Finset (Ideal O)) (B : actualAllocations s.pools C)
    (τ : Character) (t T H : ℝ) : ℝ :=
  let s':=child s C R B τ t
  let S:=finiteColumns (Fintype.piFinset s'.pools)
  (gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I:supportedColumns S=>CoupledFirst.coefficient s'
      (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) 1
        (K*markedProduct B.val)
        (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F ((D*C)*J)))
      (R*C) L I*((Real.sqrt T:ℂ)⁻¹*rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re

theorem actual_marked_allocation_main
    (s : Input ι) (A₁ A₂ D K C R seed L : Ideal O) (F : Ideal O→ℂ)
    (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hmarked : ∀Q∈P,∀i,∀J∈s.pools (Sum.inl i),¬Q∣J)
    (τ : Character) (t T : ℝ) (n : ℤ) (Z ell upper M Bcap : ℝ)
    (hZ : 1<Z) (hell : 0<ell) (hscale : 0≤M+6*upper)
    (hlower : ∀Q∈P,Z^ell≤(Q.absNorm:ℝ))
    (hupper : ∀Q∈P,(Q.absNorm:ℝ)≤Z^upper)
    (hsize : 2*(Bcap/ell)≤(P.card:ℝ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : ∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      sourceRadius (child s C R B τ t)≤Z^Bcap)
    (hdyad : dyadicScale n≤Z^M) :
    (∑'z:O,dyadicWeight n (normValue z)*
      ‖CoupledFirst.allocatedPolynomial (original s R seed)
        (markedSourceModifier A₁ A₂ D K F) C L τ t T z‖^2)≤
      ((actualAllocations s.pools C).card:ℝ)*
        ∑B:actualAllocations s.pools C,‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
          ((P.card:ℝ)⁻¹*((M+6*upper)/ell)*
            correctedChildGaussEnergy s A₁ A₂ D K C R L F P B τ t T (Z^(M+6*upper))) := by
  apply (actual_allocation_dyadic_energy s (markedSourceModifier A₁ A₂ D K F)
    C R seed L τ t T n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  by_cases hf : frozenCoefficient B.val C R s.ν s.W s.P=0
  · simp only [hf,norm_zero,zero_pow (by norm_num:2≠0),zero_mul,le_refl]
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hh := actual_marked_main_ideal_coefficient (child s C R B τ t)
      (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (D*C) (K*markedProduct B.val) (R*C) L
      F (fun I=>(Real.sqrt T:ℂ)⁻¹*rowWeight τ fixedBadMask 1 1 t I) P hP hp hbad
      (fun Q hQ i J hJ=>hmarked Q hQ i.val J hJ)
      n Z ell upper M Bcap hZ hell hscale hlower hupper hsize hz₁ hz₂ (hsource B hf) hdyad
    simp_rw [actual_marked_child_polynomial]
    dsimp only [correctedChildGaussEnergy]
    generalize hs : child s C R B τ t=s' at hh ⊢
    convert hh using 1
    · exact source_gauss_dyadic_pool_decEq (ι:=CenteredMomentCommonProfile.liveIndices B.val)
        _ _ s'.pools
        (fun I=>CoupledFirst.coefficient s'
          (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
            (D*C) (K*markedProduct B.val) F) (R*C) L I*
              ((Real.sqrt T:ℂ)⁻¹*rowWeight τ fixedBadMask 1 1 t I)) n
    · apply congrArg (fun e:ℂ=>(P.card:ℝ)⁻¹*((M+6*upper)/ell)*e.re)
      exact source_gauss_energy_pool_decEq (ι:=CenteredMomentCommonProfile.liveIndices B.val)
        _ _ s'.pools
        (fun I=>CoupledFirst.coefficient s'
          (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) 1
            (K*markedProduct B.val)
            (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F ((D*C)*J)))
          (R*C) L I*((Real.sqrt T:ℂ)⁻¹*rowWeight τ fixedBadMask 1 1 t I))
        ballProfile (Z^(M+6*upper))

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_allocation_main
