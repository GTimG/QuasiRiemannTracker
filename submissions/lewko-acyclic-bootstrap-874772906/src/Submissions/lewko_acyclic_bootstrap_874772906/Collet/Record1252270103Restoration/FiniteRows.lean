/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.Contract

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths Record1252270103KernelMass
open HeckeFamily CenteredMomentSourceMass CenteredMomentHeckeExpansion
open CenteredMomentRetainedEnergy CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

def pairProfile (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (n : IdealPair) : ℂ :=
  W₁ ((Ideal.absNorm n.1:ℝ)/X₁)*W₂ ((Ideal.absNorm n.2:ℝ)/X₂)

def holePairPool (b X₁ X₂ : ℝ) : Finset IdealPair :=
  (plainPairPool b X₁ X₂).filter (fun n=>ordinarySmallHole n.1 n.2)

def ordinaryHolePlainSum (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  ∑ n ∈ holePairPool b X₁ X₂, ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n

theorem plainPairPool_nonzero {b X₁ X₂ : ℝ} {n : IdealPair}
    (hn : n ∈ plainPairPool b X₁ X₂) : n.1≠0 ∧ n.2≠0 := by
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hn
  exact ⟨(mem_idealBall _ _).mp hi |>.1,(mem_idealBall _ _).mp hj |>.1⟩

theorem ordinarySmallHole_iff_good {I J : Ideal O} (hI : I≠0) (hJ : J≠0) :
    ordinarySmallHole I J ↔ GoodPair (I,J) := by
  constructor
  · intro h
    refine ⟨hI,hJ,?_⟩
    intro P hp
    by_contra hn
    have hprime : Prime P := by
      rcases Finset.mem_union.mp hp with hi|hj
      · exact primeSupport_prime hi
      · exact primeSupport_prime hj
    have hm : (⟨P,hprime⟩ : PrimeIdeal) ∈ smallPrimes :=
      (mem_smallPrimes _).mpr (show Ideal.absNorm P<16 from Nat.lt_of_not_ge hn)
    obtain ⟨hi,hj⟩ := h ⟨P,hprime⟩ hm
    rcases Finset.mem_union.mp hp with hpi|hpj
    · have hx : P ∈ (factorization I).support := by
        simpa only [support_factorization,primeSupport,OAI.IdealMobiusDivisorSum.primeSupport] using hpi
      exact (Finsupp.mem_support_iff.mp hx) hi
    · have hx : P ∈ (factorization J).support := by
        simpa only [support_factorization,primeSupport,OAI.IdealMobiusDivisorSum.primeSupport] using hpj
      exact (Finsupp.mem_support_iff.mp hx) hj
  · intro h P hP
    have hsmall := (mem_smallPrimes P).mp hP
    constructor
    · apply valuation_eq_zero_of_not_mem
      intro hp
      have hh := h.2.2 P.val (Finset.mem_union_left _ hp)
      omega
    · apply valuation_eq_zero_of_not_mem
      intro hp
      have hh := h.2.2 P.val (Finset.mem_union_right _ hp)
      omega

theorem holePairPool_good {b X₁ X₂ : ℝ} {n : IdealPair}
    (hn : n ∈ holePairPool b X₁ X₂) : GoodPair n := by
  obtain ⟨hpool,hhole⟩ := Finset.mem_filter.mp hn
  exact (ordinarySmallHole_iff_good (plainPairPool_nonzero hpool).1
    (plainPairPool_nonzero hpool).2).mp hhole

theorem squarefreePlainSum_eq_hole_sum (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    squarefreePlainSum ψ W₁ W₂ b X₁ X₂ =
      ∑ n ∈ holePairPool b X₁ X₂, (squarefreeIndicator (n.1*n.2) : ℂ)*ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n := by
  rw [holePairPool,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  unfold pairProfile
  split_ifs <;> ring

theorem pairProfile_multiply (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (d a : IdealPair)
    :
    pairProfile W₁ W₂ X₁ X₂ (multiplyPair d a) =
      pairProfile W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) a := by
  unfold pairProfile multiplyPair
  simp only [map_mul,Nat.cast_mul]
  rw [div_div_eq_mul_div,div_div_eq_mul_div]
  congr 2 <;> ring

 theorem rowTwistedSum_eq_finite (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X) (hs : Function.support W⊆Set.Iic b) :
    rowTwistedSum η m A z W t X = ∑ I ∈ idealBall (b*X), rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := by
  rw [rowTwistedSum_eq_weight]
  apply tsum_eq_sum
  intro I hI
  by_cases hz : I=0
  · rw [hz,map_zero,zero_mul]
  · have hw : W ((Ideal.absNorm I:ℝ)/X)=0 := by
      by_contra hn
      exact hI ((mem_idealBall _ _).mpr ⟨hz,(div_le_iff₀ hX).mp (hs hn)⟩)
    rw [hw,mul_zero]

theorem ordinary_product_eq_pair_sum (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b) :
    rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂ =
      ∑ n ∈ plainPairPool b X₁ X₂, rowWeight η m A z t (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n := by
  rw [rowTwistedSum_eq_finite η m A z t W₁ b X₁ hX₁ hs₁,
    rowTwistedSum_eq_finite η m A z t W₂ b X₂ hX₂ hs₂]
  rw [Finset.sum_mul_sum,plainPairPool,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [map_mul]
  unfold pairProfile
  ring

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.ordinary_product_eq_pair_sum
