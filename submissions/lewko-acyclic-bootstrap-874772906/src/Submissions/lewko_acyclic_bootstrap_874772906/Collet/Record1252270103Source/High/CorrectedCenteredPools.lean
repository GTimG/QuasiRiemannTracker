/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact Newton cofactor image is the scaled ordinary-hole pool, including
empty fibers. Prime norms at least16 preserve the ordinary-only hole. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.NewtonRowsActual
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CenteredExpand
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

lemma prime_product_support (S:Finset (Ideal O))(hp:∀p∈S,Prime p) :
    primeSupport (∏p∈S,p)=S := by
  have h:UniqueFactorizationMonoid.normalizedFactors (∏p∈S,p)=S.val := by
    simpa using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
      (m:=S.val) (fun p hpS=>hp p hpS)
  simp only [primeSupport,OAI.IdealMobiusDivisorSum.primeSupport,h,Finset.val_toFinset]

lemma newton_divisor_pair_good (P S A:Finset (Ideal O))(hS:S⊆P)(hA:A⊆S)
    (hp:∀p∈P,Prime p)(hN:∀p∈P,16≤p.absNorm) : GoodPair (newtonDivisorPair S A) := by
  have hpA:∀p∈A,Prime p:=fun p h=>hp p (hS (hA h))
  have hpB:∀p∈S\A,Prime p:=fun p h=>hp p (hS (Finset.mem_sdiff.mp h).1)
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun p h=>(hpA p h).ne_zero),
    Finset.prod_ne_zero_iff.mpr (fun p h=>(hpB p h).ne_zero),?_⟩
  intro p hm
  change p∈primeSupport (∏q∈A,q)∪primeSupport (∏q∈S\A,q) at hm
  rw [prime_product_support A hpA,prime_product_support (S\A) hpB] at hm
  rcases Finset.mem_union.mp hm with h|h
  · exact hN p (hS (hA h))
  · exact hN p (hS (Finset.mem_sdiff.mp h).1)

/-- No assumption that the selected divisor fiber is nonempty is needed. -/
theorem newton_residual_hole_pool (d:IdealPair)(hd:GoodPair d)(b X₁ X₂:ℝ) :
    newtonResidualPairs (holePairPool b X₁ X₂) d=
      holePairPool b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  have hdz:d.1≠0 ∧ d.2≠0:=⟨hd.1,hd.2.1⟩
  ext a
  constructor
  · intro ha
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨hn,hi,hj⟩:=Finset.mem_filter.mp hn
    have hg:=holePairPool_good hn
    have ha:=goodPair_of_dvd (n:=n) (d:=cofactorPair n.1 n.2 d) hg (idealCofactor_dvd hi) (idealCofactor_dvd hj)
    have he:=newton_cofactor_reconstruct d n ⟨hi,hj⟩
    apply Finset.mem_filter.mpr
    refine ⟨(plainPairPool_multiply_iff hdz).mp ?_,(ordinarySmallHole_iff_good ha.1 ha.2.1).mpr ha⟩
    rw [he]
    exact (Finset.mem_filter.mp hn).1
  · intro ha
    have hg:=holePairPool_good ha
    have hm:=goodPair_multiply hd hg
    have hn:multiplyPair d a∈holePairPool b X₁ X₂ := by
      apply Finset.mem_filter.mpr
      exact ⟨(plainPairPool_multiply_iff hdz).mpr (Finset.mem_filter.mp ha).1,
        (ordinarySmallHole_iff_good hm.1 hm.2.1).mpr hm⟩
    apply Finset.mem_image.mpr
    refine ⟨multiplyPair d a,Finset.mem_filter.mpr ⟨hn,dvd_mul_right _ _,dvd_mul_right _ _⟩,?_⟩
    exact cofactorPair_multiply d a hdz

end
end QRH.Record1252270103Source.High.CorrectedCentered
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.newton_divisor_pair_good
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.newton_residual_hole_pool
