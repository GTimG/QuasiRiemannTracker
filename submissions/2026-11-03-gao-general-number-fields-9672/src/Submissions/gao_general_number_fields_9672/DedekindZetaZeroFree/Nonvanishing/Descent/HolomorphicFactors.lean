/-
2026-11-03 frozen baseline packaging by Zhongpai Gao (https://github.com/Gaozhongpai).
This support module retains the registered PR #114 native source at 09afbb4ce6570c1615d58509dc197fc9f0956b7d,
whose endpoint is 31/32. The separate Refinement9672 namespace supplies the new candidate.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672.
Original declaration namespaces and source attribution are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Descent/HolomorphicFactors.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Main

@[expose] public section

namespace DedekindZetaZeroFree.HeckeCorollary

theorem factor_ne_zero_off_one
    (L : Type) [Field L] [NumberField L] (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfactor : ∀ s : ℂ, 1 < s.re → f s * g s = NumberField.dedekindZeta L s)
    (s : ℂ) (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) : f s ≠ 0 := by
  obtain ⟨z, hz, hzeq, hzne⟩ := dedekindZeta_ne_zero L
  have heq : Set.EqOn (fun t => f t * g t) z ({1}ᶜ : Set ℂ) :=
    continuation_unique_off_one _ _ (hf.mul hg) hz
      (fun t ht => (hfactor t ht).trans (hzeq t ht).symm)
  intro hzero
  have hprod := heq (show s ∈ ({1}ᶜ : Set ℂ) from hs1)
  change f s * g s = z s at hprod
  rw [hzero, zero_mul] at hprod
  exact hzne s hs hs1 hprod.symm

end DedekindZetaZeroFree.HeckeCorollary
