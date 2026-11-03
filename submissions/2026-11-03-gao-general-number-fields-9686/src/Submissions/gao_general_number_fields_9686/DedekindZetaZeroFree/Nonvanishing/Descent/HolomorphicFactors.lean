/-
2026-11-03 refinement by Zhongpai Gao (https://github.com/Gaozhongpai).
The following header records the PR #114 source provenance at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
This file now contains the native parameter refinement at
829193272c1eaf223bb7228fbfb9003f414808e9; local imports are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and all source attribution are retained.
Native compilation and tracker admission remain pending; see Candidate.Provenance.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Descent/HolomorphicFactors.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Main

@[expose] public section

namespace DedekindZetaZeroFree.HeckeCorollary

theorem factor_ne_zero_off_one
    (L : Type) [Field L] [NumberField L] (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfactor : ∀ s : ℂ, 1 < s.re → f s * g s = NumberField.dedekindZeta L s)
    (s : ℂ) (hs : 4843 / 5000 < s.re) (hs1 : s ≠ 1) : f s ≠ 0 := by
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
