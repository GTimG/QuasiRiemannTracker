/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual marked balanced first budget enters corrected MAIN with all labels,
actual allocation counts and original frozen coefficients retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBalancedColumns
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalAllocationMain
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentFirstAnnularMajorant CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstAmplificationChoice
open CenteredMomentPrimePool CenteredMomentLogDyadic Cycle61InitialMass
open Record1252270103Source.Collision GlobalPhysical QRH.Record1252270103Low
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

/-- MAIN is applied to the actual child polynomial after exact common
allocation. All sums remain inside the one first-column Hilbert budget. -/
theorem actual_balanced_marked_main
    (reflected : Bool) (s : Input ι) (A₁ A₂ D Kmark R seed : Ideal O)
    (F : Ideal O→ℂ) (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s (markedSourceModifier A₁ A₂ D Kmark F) R seed K Z ξ→ℂ)
    (t ell upper Bcap : ℝ)
    (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hmarked : ∀Q∈P,∀i,∀J∈s.pools (Sum.inl i),¬Q∣J)
    (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀Q∈P,Z^ell≤(Q.absNorm:ℝ))
    (hupper : ∀Q∈P,(Q.absNorm:ℝ)≤Z^upper)
    (hsize : 2*(Bcap/ell)≤(P.card:ℝ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :
    let modifier:=markedSourceModifier A₁ A₂ D Kmark F
    let src:=geometryFirstSource s modifier R seed K Z ξ hK key
    let C:=geometryColumnIdeal reflected s modifier R seed K Z ξ hK key
    let τ:=geometryColumnCharacter reflected s modifier R seed K Z ξ hK key
    ∀radius : FirstColumnIndex src→ℝ,
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),0≤radius j+6*upper) →
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),∀n∈bands (src j.1).H0,
      dyadicScale n≤Z^(radius j)) →
    (∀j∈firstLiveColumns src (fun _=>logAnnulus),∀B:actualAllocations s.pools (C j),
      frozenCoefficient B.val (C j) R s.ν s.W s.P≠0→
      sourceRadius (child s (C j) R B (τ j) t)≤Z^Bcap) →
    balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key weight t ≤
      ∑j∈firstLiveColumns src (fun _=>logAnnulus),
        ‖balancedColumnScalar reflected s modifier R seed K Z ξ M A hK key weight j‖^2*
          (((bands (src j.1).H0).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)*
            ∑B:actualAllocations s.pools (C j),‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*
              ((P.card:ℝ)⁻¹*((radius j+6*upper)/ell)*
                correctedChildGaussEnergy s A₁ A₂ D Kmark (C j) R j.2.1.val F P B
                  (τ j) t (volume s) (Z^(radius j+6*upper)))) := by
  intro modifier src C τ radius hscale hband hsource
  unfold balancedLiveBudget
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _≤∑n∈bands (src j.1).H0,((actualAllocations s.pools (C j)).card:ℝ)*
        ∑B:actualAllocations s.pools (C j),‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*
          ((P.card:ℝ)⁻¹*((radius j+6*upper)/ell)*
            correctedChildGaussEnergy s A₁ A₂ D Kmark (C j) R j.2.1.val F P B
              (τ j) t (volume s) (Z^(radius j+6*upper))) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      change ‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*
        (∑'z:O,dyadicWeight n (normValue z)*
          ‖childPolynomial s (markedSourceModifier A₁ A₂ D Kmark F) (C j) R j.2.1.val B
            (τ j) t (volume s) z‖^2)≤_
      by_cases hf : frozenCoefficient B.val (C j) R s.ν s.W s.P=0
      · simp only [hf,norm_zero,zero_pow (by norm_num:2≠0),zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hh := actual_marked_main_ideal_coefficient (child s (C j) R B (τ j) t)
          (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (D*C j)
          (Kmark*markedProduct B.val) (R*C j) j.2.1.val F
          (fun I=>(Real.sqrt (volume s):ℂ)⁻¹*rowWeight (τ j) fixedBadMask 1 1 t I)
          P hP hp hbad (fun Q hQ i J hJ=>hmarked Q hQ i.val J hJ)
          n Z ell upper (radius j) Bcap hZ hell (hscale j hj) hlower hupper hsize
          hz₁ hz₂ (hsource j hj B hf) (hband j hj n hn)
        simp_rw [actual_marked_child_polynomial]
        dsimp only [correctedChildGaussEnergy]
        generalize hs : child s (C j) R B (τ j) t=s' at hh ⊢
        convert hh using 1
        · exact source_gauss_dyadic_pool_decEq (ι:=liveIndices B.val) _ _ s'.pools
            (fun I=>coefficient s'
              (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
                (D*C j) (Kmark*markedProduct B.val) F) (R*C j) j.2.1.val I*
              ((Real.sqrt (volume s):ℂ)⁻¹*rowWeight (τ j) fixedBadMask 1 1 t I)) n
        · apply congrArg (fun e:ℂ=>(P.card:ℝ)⁻¹*((radius j+6*upper)/ell)*e.re)
          exact source_gauss_energy_pool_decEq (ι:=liveIndices B.val) _ _ s'.pools
            (fun I=>coefficient s'
              (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) 1
                (Kmark*markedProduct B.val)
                (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F ((D*C j)*J)))
              (R*C j) j.2.1.val I*((Real.sqrt (volume s):ℂ)⁻¹*rowWeight (τ j) fixedBadMask 1 1 t I))
            ballProfile (Z^(radius j+6*upper))
    _=_ := by simp only [Finset.sum_const,nsmul_eq_mul];ring
end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_marked_main
