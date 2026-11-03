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
Original path: DedekindZetaZeroFree/Nonvanishing/Descent/HolomorphicFactors.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Main

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.HeckeCorollary

theorem factor_ne_zero_off_one
    (L : Type) [Field L] [NumberField L] (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfactor : ∀ s : ℂ, 1 < s.re → f s * g s = NumberField.dedekindZeta L s)
    (s : ℂ) (hs : 1209 / 1250 < s.re) (hs1 : s ≠ 1) : f s ≠ 0 := by
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

end Refinement9672
