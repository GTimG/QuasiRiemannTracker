/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.GlobalIdentities

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
abbrev IdealPair := Ideal O × Ideal O

def multiplyPair (d a : IdealPair) : IdealPair := (d.1*a.1,d.2*a.2)

def expandedAt (n : IdealPair) : Finset (IdealPair × IdealPair) := by
  classical
  exact (idealDivisors n.1 ×ˢ idealDivisors n.2).image (fun d => (d,cofactorPair n.1 n.2 d))

def expandedPairs (D : Finset IdealPair) : Finset (IdealPair × IdealPair) := by
  classical
  exact D.biUnion expandedAt

theorem expandedAt_reconstruct {n : IdealPair} (hn : n.1 ≠ 0 ∧ n.2 ≠ 0)
    {p : IdealPair × IdealPair} (hp : p ∈ expandedAt n) : multiplyPair p.1 p.2=n := by
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
  apply Prod.ext
  · exact idealCofactor_mul ((mem_idealDivisors hn.1).mp hi)
  · exact idealCofactor_mul ((mem_idealDivisors hn.2).mp hj)

theorem expandedAt_disjoint {n m : IdealPair} (hn : n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hm : m.1 ≠ 0 ∧ m.2 ≠ 0) (hne : n ≠ m) : Disjoint (expandedAt n) (expandedAt m) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hne ((expandedAt_reconstruct hn hp).symm.trans (expandedAt_reconstruct hm hq))

theorem finite_divisor_reindex (D : Finset IdealPair) (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (F : IdealPair → IdealPair → IdealPair → ℂ) :
    (∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2, F n d (cofactorPair n.1 n.2 d)) =
      ∑ p ∈ expandedPairs D, F (multiplyPair p.1 p.2) p.1 p.2 := by
  classical
  rw [expandedPairs,Finset.sum_biUnion (by
    intro n hn m hm hne
    exact expandedAt_disjoint (hnz n hn) (hnz m hm) hne)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [expandedAt,Finset.sum_image (by
    intro d hd e he h
    exact congrArg Prod.fst h)]
  apply Finset.sum_congr rfl
  intro d hd
  have heq := expandedAt_reconstruct (hnz n hn)
    (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
  rw [heq]

def divisorPool (D : Finset IdealPair) : Finset IdealPair := by
  classical
  exact (expandedPairs D).image Prod.fst

def residualPool (D : Finset IdealPair) (d : IdealPair) : Finset IdealPair := by
  classical
  exact ((expandedPairs D).filter (fun p => p.1=d)).image Prod.snd

theorem expandedPairs_grouped (D : Finset IdealPair) (F : IdealPair → IdealPair → ℂ) :
    (∑ p ∈ expandedPairs D, F p.1 p.2) =
      ∑ d ∈ divisorPool D, ∑ a ∈ residualPool D d, F d a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := expandedPairs D) (t := divisorPool D) (g := Prod.fst)
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) (fun p => F p.1 p.2)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [residualPool,Finset.sum_image (by
    intro p hp q hq h
    apply Prod.ext
    · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    · exact h)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem ideal_norm_one_le {I : Ideal O} (hI : I ≠ 0) : (1:ℝ) ≤ Ideal.absNorm I := by
  have hn : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  exact_mod_cast hn

theorem goodPair_of_dvd {n d : IdealPair} (hn : GoodPair n) (hi : d.1 ∣ n.1) (hj : d.2 ∣ n.2) : GoodPair d := by
  have hdi := ne_zero_of_dvd_ne_zero hn.1 hi
  have hdj := ne_zero_of_dvd_ne_zero hn.2.1 hj
  refine ⟨hdi,hdj,?_⟩
  intro P hP
  apply hn.2.2 P
  exact Finset.union_subset_union (primeSupport_subset_of_dvd hdi hn.1 hi)
    (primeSupport_subset_of_dvd hdj hn.2.1 hj) hP

theorem expandedPairs_good {D : Finset IdealPair} (hD : ∀ n ∈ D, GoodPair n)
    {p : IdealPair × IdealPair} (hp : p ∈ expandedPairs D) : GoodPair p.1 ∧ GoodPair p.2 := by
  obtain ⟨n,hn,hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hd
  have hni := (hD n hn).1
  have hnj := (hD n hn).2.1
  have hdi := (mem_idealDivisors hni).mp hi
  have hdj := (mem_idealDivisors hnj).mp hj
  exact ⟨goodPair_of_dvd (hD n hn) hdi hdj,
    goodPair_of_dvd (hD n hn) (idealCofactor_dvd hdi) (idealCofactor_dvd hdj)⟩

theorem pairNorm_multiply (d a : IdealPair) : pairNorm (multiplyPair d a)=pairNorm d*pairNorm a := by
  simp only [pairNorm,multiplyPair,map_mul,Nat.cast_mul]
  ring

theorem character_pair_multiply (ψ : Ideal O →* ℂ) (d a : IdealPair) :
    ψ ((multiplyPair d a).1*(multiplyPair d a).2) = ψ (d.1*d.2)*ψ (a.1*a.2) := by
  have h : (multiplyPair d a).1*(multiplyPair d a).2 = (d.1*d.2)*(a.1*a.2) := by
    unfold multiplyPair
    dsimp only
    ring
  rw [h,map_mul]

theorem forward_finite_character_identity (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0) (ψ : Ideal O →* ℂ) (f : IdealPair → ℂ) :
    (∑ n ∈ D, (squarefreeIndicator (n.1*n.2) : ℂ)*ψ (n.1*n.2)*f n) =
    ∑ p ∈ expandedPairs D, (forwardKernel p.1.1 p.1.2 : ℂ)*
      ψ (p.1.1*p.1.2)*ψ (p.2.1*p.2.2)*f (multiplyPair p.1 p.2) := by
  classical
  calc
    _ = ∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (forwardKernel d.1 d.2 : ℂ)*ψ (n.1*n.2)*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [forward_global_divisor_identity (hnz n hn).1 (hnz n hn).2]
      push_cast
      rw [Finset.sum_mul,Finset.sum_mul]
    _ = ∑ p ∈ expandedPairs D, (forwardKernel p.1.1 p.1.2 : ℂ)*
        ψ ((multiplyPair p.1 p.2).1*(multiplyPair p.1 p.2).2)*f (multiplyPair p.1 p.2) :=
      finite_divisor_reindex D hnz (fun n d _ => (forwardKernel d.1 d.2 : ℂ)*ψ (n.1*n.2)*f n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [character_pair_multiply]
      ring

theorem inverse_finite_character_identity (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0) (ψ : Ideal O →* ℂ) (f : IdealPair → ℂ) :
    (∑ n ∈ D, ψ (n.1*n.2)*f n) =
    ∑ p ∈ expandedPairs D, (inverseKernel p.1.1 p.1.2 : ℂ)*
      ψ (p.1.1*p.1.2)*ψ (p.2.1*p.2.2)*(squarefreeIndicator (p.2.1*p.2.2) : ℂ)*
      f (multiplyPair p.1 p.2) := by
  classical
  calc
    _ = ∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (inverseKernel d.1 d.2 : ℂ)*
          (squarefreeIndicator ((cofactorPair n.1 n.2 d).1*(cofactorPair n.1 n.2 d).2) : ℂ)*ψ (n.1*n.2)*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hi := congrArg (fun z : ℤ => (z:ℂ)) (inverse_global_divisor_identity (hnz n hn).1 (hnz n hn).2)
      push_cast at hi
      calc
        ψ (n.1*n.2)*f n = (1:ℂ)*ψ (n.1*n.2)*f n := by ring
        _ = _ := by rw [hi,Finset.sum_mul,Finset.sum_mul]; rfl
    _ = ∑ p ∈ expandedPairs D, (inverseKernel p.1.1 p.1.2 : ℂ)*
        (squarefreeIndicator (p.2.1*p.2.2) : ℂ)*
        ψ ((multiplyPair p.1 p.2).1*(multiplyPair p.1 p.2).2)*f (multiplyPair p.1 p.2) :=
      finite_divisor_reindex D hnz (fun n d a => (inverseKernel d.1 d.2 : ℂ)*
        (squarefreeIndicator (a.1*a.2) : ℂ)*ψ (n.1*n.2)*f n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [character_pair_multiply]
      ring

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.forward_finite_character_identity
#print axioms QRH.Record1252270103KernelMass.inverse_finite_character_identity
