/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Dedekind/MixedThetaMellinModel.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaPairMellin

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem zeta_mixedThetaModel (K : Type) [Field K] [NumberField K] :
    ∃ P : WeakFEPair ℂ, P.k = 1 ∧
      ∀ s : ℂ, 1 < s.re →
        HasMellin (fun t : ℝ => P.f t - P.f₀) s
          (zetaGammaFactor K s * NumberField.dedekindZeta K s) := by
  refine ⟨Theta.mixedThetaPair K, Theta.mixedThetaPair_k K, ?_⟩
  intro s hs
  exact Theta.hasMellin_mixedThetaPair K hs

end DedekindZetaZeroFree.AbelianQuotient
