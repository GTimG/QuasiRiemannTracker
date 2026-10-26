/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Every original live column, allocation, frozen coefficient and annular band
is counted in an absolute bound for the literal first balanced budget. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstAbsoluteBudgetChild
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBalancedColumns
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstAbsoluteBudget
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentLogDyadic QuadraticInitialBound Cycle61InitialMass
open QRH.Record1252270103Source.SecondAbsoluteEnvelope
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O
local instance firstAbsoluteBudgetSumDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem balanced_live_budget_finite {ι:Type*} [Fintype ι]
    (N:ℕ) (Cs hi whi wlo X Y Smax Amax Lmax:ℝ)
    (hCs:1≤Cs) (hhi:1≤hi) (hwhi:0≤whi) (hwlo:0<wlo) (hX:1≤X) (hY:0≤Y)
    (hSmax:0≤Smax) (hAmax:0≤Amax) (hLmax:0≤Lmax)
    (s:Input ι) (modifier:Tuple ι→ℂ)
    (hN:Fintype.card ι≤N) (hM:∀i,s.M i≤Cs)
    (hslot0:∀i,1≤s.hi i) (hslot:∀i,s.hi i≤hi) (hP:∀i,1≤s.P i)
    (hb₁:0≤s.b₁) (hb₂:0≤s.b₂) (hsource:sourceRadius s≤Y)
    (hmod:∀v,‖modifier v‖≤2)
    (W₁ W₂:𝓢(ℝ,ℂ)) (he₁:s.W₁=W₁) (he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (reflected:Bool) (R seed:Ideal O) (K Z ξ M A:ℝ) (hK:0<K) (key:ℤ×(Fin 5→ℤ))
    (weight:SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (hscalar:∀j∈firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK key) (fun _=>logAnnulus),
      ‖balancedColumnScalar reflected s modifier R seed K Z ξ M A hK key weight j‖^2≤Smax)
    (halloc:∀j∈firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK key) (fun _=>logAnnulus),
      ((actualAllocations s.pools (geometryColumnIdeal reflected s modifier R seed K Z ξ hK key j)).card:ℝ)^2≤Amax)
    (hlive:((firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK key) (fun _=>logAnnulus)).card:ℝ)≤Lmax)
    (hband:∀j∈firstLiveColumns (geometryFirstSource s modifier R seed K Z ξ hK key) (fun _=>logAnnulus),
      ∀n∈bands (geometryFirstSource s modifier R seed K Z ξ hK key j.1).H0,dyadicScale n≤X)
    (t:ℝ) :
    balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key weight t≤
      Lmax*Smax*7*Amax*(Cs^N)^2*diagonalControl ballProfile*X*Y*
        (massConstant N Cs hi whi)^2*
        (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s := by
  let src:=geometryFirstSource s modifier R seed K Z ξ hK key
  let C:=geometryColumnIdeal reflected s modifier R seed K Z ξ hK key
  let τ:=geometryColumnCharacter reflected s modifier R seed K Z ξ hK key
  let E:=diagonalControl ballProfile*X*Y*(massConstant N Cs hi whi)^2*
    (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s
  have hE:0≤E:=by
    have hd := diagonalControl_nonneg ballProfile
    have hv := (volume_pos s).le
    dsimp [E]
    positivity
  have hchild (j:FirstColumnIndex src) (hj:j∈firstLiveColumns src (fun _=>logAnnulus))
      (n:ℤ) (hn:n∈bands (src j.1).H0) (B:actualAllocations s.pools (C j)) :
      (∑'z:O,dyadicWeight n (normValue z)*
        ‖childPolynomial s modifier (C j) R j.2.1.val B (τ j) t (volume s) z‖^2)≤E :=
    child_dyadic_absolute N Cs hi whi wlo X Y hCs hhi hwhi hwlo hX hY s modifier
      hN hM hslot0 hslot hP hb₁ hb₂ hsource hmod W₁ W₂ he₁ he₂ hs₁ hs₂
      (C j) R j.2.1.val B (τ j) t n (hband j hj n hn)
  have hsum (j:FirstColumnIndex src) (hj:j∈firstLiveColumns src (fun _=>logAnnulus))
      (n:ℤ) (hn:n∈bands (src j.1).H0) :
      ((actualAllocations s.pools (C j)).card:ℝ)*
        (∑B:actualAllocations s.pools (C j),‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*
          (∑'z:O,dyadicWeight n (normValue z)*
            ‖childPolynomial s modifier (C j) R j.2.1.val B (τ j) t (volume s) z‖^2))≤
      Amax*(Cs^N)^2*E := by
    calc
      _≤((actualAllocations s.pools (C j)).card:ℝ)*
          (∑_B:actualAllocations s.pools (C j),(Cs^N)^2*E) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro B _
        apply (mul_le_mul_of_nonneg_left (hchild j hj n hn B) (sq_nonneg _)).trans
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (MarkedMainRemainder.selected_frozen_norm s N Cs hN hCs hM (C j) R B) 2) hE
      _=((actualAllocations s.pools (C j)).card:ℝ)^2*((Cs^N)^2*E) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
        ring
      _≤Amax*((Cs^N)^2*E) := mul_le_mul_of_nonneg_right (halloc j hj) (mul_nonneg (sq_nonneg _) hE)
      _=_ := by ring
  unfold balancedLiveBudget
  change (∑j∈firstLiveColumns src (fun _=>logAnnulus),_ )≤_
  calc
    _≤∑_j∈firstLiveColumns src (fun _=>logAnnulus),Smax*(7*Amax*(Cs^N)^2*E) := by
      apply Finset.sum_le_sum
      intro j hj
      have hi : (∑n∈bands (src j.1).H0,
          ((actualAllocations s.pools (C j)).card:ℝ)*
          ∑B:actualAllocations s.pools (C j),‖frozenCoefficient B.val (C j) R s.ν s.W s.P‖^2*
          (∑'z:O,dyadicWeight n (normValue z)*
            ‖childPolynomial s modifier (C j) R j.2.1.val B (τ j) t (volume s) z‖^2))≤7*Amax*(Cs^N)^2*E := by
        calc
          _≤∑_n∈bands (src j.1).H0,Amax*(Cs^N)^2*E := Finset.sum_le_sum (fun n hn=>hsum j hj n hn)
          _=((bands (src j.1).H0).card:ℝ)*(Amax*(Cs^N)^2*E) := by simp
          _≤7*(Amax*(Cs^N)^2*E) := mul_le_mul_of_nonneg_right
            (bands_card _ (src j.1).H0_pos) (by positivity)
          _=_ := by ring
      apply (mul_le_mul_of_nonneg_left hi (sq_nonneg _)).trans
      exact mul_le_mul_of_nonneg_right (hscalar j hj) (by positivity)
    _=((firstLiveColumns src (fun _=>logAnnulus)).card:ℝ)*(Smax*(7*Amax*(Cs^N)^2*E)) := by simp
    _≤Lmax*(Smax*(7*Amax*(Cs^N)^2*E)) := mul_le_mul_of_nonneg_right hlive (by positivity)
    _=_ := by dsimp [E];ring

end
end QRH.Record1252270103Source.FirstAbsoluteBudget
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.balanced_live_budget_finite
