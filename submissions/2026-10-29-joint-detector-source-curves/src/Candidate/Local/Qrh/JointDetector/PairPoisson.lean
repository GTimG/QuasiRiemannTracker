/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SelectedKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

/-! Exact arithmetic bridges for selected pair reflection. The Poisson identity
below is on elements in the primitive-character orientation. Transfer from a
good-ideal sum still requires unit reindexing and its original bad-place mask. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

/-- Identify the literal ideal-row feature with the finite primitive row.
The equality includes every natural zero. -/
theorem idealRow_prime_product {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) :
    idealRowHom z (∏ i ∈ S, P i) = finiteSquarefreeRow P hg S z := by
  rw [map_prod]
  unfold finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime z (P i) (hg i)

/-- Exact Poisson for a coprime pair of squarefree ideal products. Its Gauss
factor remains the actual normalized CRT sum, with left color 1 and right 5. -/
theorem ideal_prime_pair_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, (idealRowHom z (∏ i ∈ S, P i) *
        star (idealRowHom z (∏ i ∈ Finset.univ \ S, P i))) *
        W (‖eisEmbedding z‖ ^ 2 / L)) =
      ((L : ℂ) * canonicalNormalizedGauss P hcop hg
        (fun i => if i ∈ S then 1 else 5) /
          (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)) *
      ∑' h : O, star (idealRowHom h (∏ i ∈ S, P i) *
        star (idealRowHom h (∏ i ∈ Finset.univ \ S, P i))) *
        paperRadialFourier W
          (L * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2) := by
  simp_rw [idealRow_prime_product P hg]
  exact canonical_disjoint_pair_radial_poisson P hcop hg hchar S W L hL

theorem ideal_prime_pair_zero_frequency {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) :
    idealRowHom 0 (∏ i ∈ S, P i) *
      star (idealRowHom 0 (∏ i ∈ Finset.univ \ S, P i)) = 0 := by
  simp_rw [idealRow_prime_product P hg]
  rw [← finiteSexticRow_disjoint_pair P hcop hg S]
  exact finiteSexticRow_zero P hg (fun i => if i ∈ S then 1 else 5)

/-- Equal finite reciprocity-ray states cancel the pair's orientation phases.
This is pointwise on good primary source elements; no source mask is removed. -/
theorem same_ray_pair_orientation (a b n : O)
    (hpa : lambda ^ 2 ∣ a - 1) (hpb : lambda ^ 2 ∣ b - 1)
    (hpn : lambda ^ 2 ∣ n - 1)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hn : Supported (Ideal.span {n}))
    (hray : residue a = residue b) :
    idealRowHom a (Ideal.span {n}) * star (idealRowHom b (Ideal.span {n})) =
      idealRowHom n (Ideal.span {a}) * star (idealRowHom n (Ideal.span {b})) := by
  rw [idealRowHom_primary_reciprocity_ray n a hpn hpa hn ha,
    idealRowHom_primary_reciprocity_ray n b hpn hpb hn hb, ← hray, star_mul]
  have hsign : MixedCrossSeparation.quadraticRayPair (residue n) (residue a) *
      star (MixedCrossSeparation.quadraticRayPair (residue n) (residue a)) = 1 := by
    rw [quadraticRayPair_eq_sign _ _ (supported_residue_odd n hn) (supported_residue_odd a ha)]
    simp only [star_intCast]
    have hs := quadraticRaySign_sq (residue n) (residue a)
      (supported_residue_odd n hn) (supported_residue_odd a ha)
    rw [pow_two] at hs
    exact_mod_cast hs
  calc
    _ = (MixedCrossSeparation.quadraticRayPair (residue n) (residue a) *
      star (MixedCrossSeparation.quadraticRayPair (residue n) (residue a))) *
      (idealRowHom n (Ideal.span {a}) * star (idealRowHom n (Ideal.span {b}))) := by ring
    _ = _ := by rw [hsign, one_mul]

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.ideal_prime_pair_poisson
#print axioms Qrh.JointDetector.ideal_prime_pair_zero_frequency
#print axioms Qrh.JointDetector.same_ray_pair_orientation
