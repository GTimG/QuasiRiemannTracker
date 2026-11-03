/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Nonvanishing/Hecke/GaloisCharacter.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Descent.HolomorphicFactors
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.AbelianFactorizationNonvanishingAtOne

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.HeckeCorollary

open scoped NumberField
open AbelianQuotient IsDedekindDomain

private instance galoisCharacterCommGroup (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsAbelianGalois K L] : CommGroup (L ≃ₐ[K] L) :=
  { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := fun σ τ => mul_comm' σ τ }

theorem galoisCharacter_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (ρ : ComplexDual (L ≃ₐ[K] L)) (hρ : ρ ≠ 1) :
    ∃ (m : Ideal (𝓞 K)) (χ : RayClassCharacter K m) (f : ℂ → ℂ),
      m ≠ ⊥ ∧ ¬ χ.IsPrincipal ∧
      (∀ (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
        W.asIdeal.LiesOver p.asIdeal → χ p.asIdeal = primeArtinValue ρ W) ∧
      Differentiable ℂ f ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      (∀ s, 1209 / 1250 < s.re → f s ≠ 0) := by
  obtain ⟨m, χ, hm, hm1, hχ1, hnonprincipal, hprime⟩ := conductorRayRealization K L
  let D := ComplexDual (L ≃ₐ[K] L)
  let E := {σ : D // σ ≠ 1}
  choose F hF hsum using fun σ : E =>
    rayCharacterEntire K (m σ.1) (hm σ.1) (χ σ.1) (hnonprincipal σ.1 σ.2)
  have hfactor (s : ℂ) (hs : 1 < s.re) :
      NumberField.dedekindZeta L s = (∏ σ : E, F σ s) * NumberField.dedekindZeta K s := by
    rw [nontrivialCharacterFactorization K L m χ hm hprime hχ1 s hs]
    congr 1
    exact Finset.prod_congr rfl fun σ _ => (hsum σ s hs).tsum_eq
  let r : E := ⟨ρ, hρ⟩
  refine ⟨m ρ, χ ρ, F r, hm ρ, hnonprincipal ρ hρ, hprime ρ, hF r, hsum r, ?_⟩
  intro s hs
  by_cases hs1 : s = 1
  · subst s
    exact zetaFactorization_factor_one_ne_zero K L F
      (fun σ => (hF σ).continuous.continuousAt) hfactor r
  obtain ⟨z, hz, hzeq⟩ := zetaContinuation K
  let g : ℂ → ℂ := fun t => (∏ σ ∈ Finset.univ.erase r, F σ t) * z t
  have hprodDiff : Differentiable ℂ (fun t => ∏ σ ∈ Finset.univ.erase r, F σ t) := by
    apply Differentiable.fun_finsetProd
    intro σ _
    exact hF σ
  have hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ) :=
    hprodDiff.differentiableOn.mul hz
  apply factor_ne_zero_off_one L (F r) g (hF r).differentiableOn hg _ s hs hs1
  intro t ht
  dsimp [g]
  rw [hzeq t ht, hfactor t ht]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  ring

end DedekindZetaZeroFree.HeckeCorollary

end Refinement9672
