/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.FiniteRows

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentSourceMass
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem goodPair_multiply {d a : IdealPair} (hd : GoodPair d) (ha : GoodPair a) :
    GoodPair (multiplyPair d a) := by
  have hdi := (ordinarySmallHole_iff_good hd.1 hd.2.1).mpr hd
  have hai := (ordinarySmallHole_iff_good ha.1 ha.2.1).mpr ha
  apply (ordinarySmallHole_iff_good (mul_ne_zero hd.1 ha.1) (mul_ne_zero hd.2.1 ha.2.1)).mp
  intro P hP
  obtain ⟨h₁,h₂⟩ := hdi P hP
  obtain ⟨ha₁,ha₂⟩ := hai P hP
  simp only [multiplyPair,valuation_mul hd.1 ha.1,valuation_mul hd.2.1 ha.2.1,h₁,h₂,ha₁,ha₂,add_zero,and_self]

theorem divisorPool_hole_good {b X₁ X₂ : ℝ} {d : IdealPair}
    (hd : d ∈ divisorPool (holePairPool b X₁ X₂)) : GoodPair d := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
  exact (expandedPairs_good (fun n hn=>holePairPool_good hn) hp).1

theorem expandedPairs_original {D : Finset IdealPair}
    (hnz : ∀ n ∈ D,n.1≠0 ∧ n.2≠0) {p : IdealPair×IdealPair}
    (hp : p ∈ expandedPairs D) : multiplyPair p.1 p.2 ∈ D := by
  obtain ⟨n,hn,hp⟩ := Finset.mem_biUnion.mp hp
  rw [expandedAt_reconstruct (hnz n hn) hp]
  exact hn

theorem cofactorPair_multiply (d a : IdealPair) (hd : d.1≠0 ∧ d.2≠0) :
    cofactorPair (multiplyPair d a).1 (multiplyPair d a).2 d = a := by
  apply Prod.ext
  · apply mul_left_cancel₀ hd.1
    exact idealCofactor_mul (dvd_mul_right d.1 a.1)
  · apply mul_left_cancel₀ hd.2
    exact idealCofactor_mul (dvd_mul_right d.2 a.2)

theorem plainPairPool_multiply_iff {b X₁ X₂ : ℝ} {d a : IdealPair}
    (hd : d.1≠0 ∧ d.2≠0) :
    multiplyPair d a ∈ plainPairPool b X₁ X₂ ↔
      a ∈ plainPairPool b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  have hi : 0<(Ideal.absNorm d.1:ℝ) := lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hd.1)
  have hj : 0<(Ideal.absNorm d.2:ℝ) := lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hd.2)
  simp only [plainPairPool,Finset.mem_product,mem_idealBall,multiplyPair,
    mul_ne_zero_iff,map_mul,Nat.cast_mul,hd.1,hd.2,true_and]
  have h₁ (x : ℝ) : (Ideal.absNorm d.1:ℝ)*x≤b*X₁ ↔ x≤b*(X₁/Ideal.absNorm d.1) := by
    rw [show b*(X₁/(Ideal.absNorm d.1:ℝ))=(b*X₁)/Ideal.absNorm d.1 by ring,
      le_div_iff₀ hi,mul_comm x]
  have h₂ (x : ℝ) : (Ideal.absNorm d.2:ℝ)*x≤b*X₂ ↔ x≤b*(X₂/Ideal.absNorm d.2) := by
    rw [show b*(X₂/(Ideal.absNorm d.2:ℝ))=(b*X₂)/Ideal.absNorm d.2 by ring,
      le_div_iff₀ hj,mul_comm x]
  rw [h₁,h₂]
  constructor
  · rintro ⟨⟨⟨_,ha₁⟩,hb₁⟩,⟨_,ha₂⟩,hb₂⟩
    exact ⟨⟨ha₁,hb₁⟩,ha₂,hb₂⟩
  · rintro ⟨⟨ha₁,hb₁⟩,ha₂,hb₂⟩
    exact ⟨⟨⟨hd.1,ha₁⟩,hb₁⟩,⟨hd.2,ha₂⟩,hb₂⟩

theorem residualPool_holePairPool {b X₁ X₂ : ℝ} {d : IdealPair}
    (hd : d ∈ divisorPool (holePairPool b X₁ X₂)) :
    residualPool (holePairPool b X₁ X₂) d =
      holePairPool b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  have hdg := divisorPool_hole_good hd
  have hdz : d.1≠0 ∧ d.2≠0 := ⟨hdg.1,hdg.2.1⟩
  ext a
  constructor
  · intro ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hp,heq⟩ := Finset.mem_filter.mp hp
    have hpa := expandedPairs_good (fun n hn=>holePairPool_good hn) hp
    have horig := expandedPairs_original
      (fun n hn=>⟨(holePairPool_good hn).1,(holePairPool_good hn).2.1⟩) hp
    rw [heq] at horig
    obtain ⟨hpool,_⟩ := Finset.mem_filter.mp horig
    apply Finset.mem_filter.mpr
    exact ⟨(plainPairPool_multiply_iff hdz).mp hpool,
      (ordinarySmallHole_iff_good hpa.2.1 hpa.2.2.1).mpr hpa.2⟩
  · intro ha
    have hag := holePairPool_good ha
    have hmul := goodPair_multiply hdg hag
    have hn : multiplyPair d a ∈ holePairPool b X₁ X₂ := by
      apply Finset.mem_filter.mpr
      exact ⟨(plainPairPool_multiply_iff hdz).mpr (Finset.mem_filter.mp ha).1,
        (ordinarySmallHole_iff_good hmul.1 hmul.2.1).mpr hmul⟩
    have he : (d,a) ∈ expandedPairs (holePairPool b X₁ X₂) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨multiplyPair d a,hn,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨d,Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
      · exact (OAI.IdealMobiusDivisorSum.mem_idealDivisors hmul.1).mpr (dvd_mul_right _ _)
      · exact (OAI.IdealMobiusDivisorSum.mem_idealDivisors hmul.2.1).mpr (dvd_mul_right _ _)
      · rw [cofactorPair_multiply d a hdz]
    exact Finset.mem_image.mpr ⟨(d,a),Finset.mem_filter.mpr ⟨he,rfl⟩,rfl⟩

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.residualPool_holePairPool
