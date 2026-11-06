/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Bilinear/GcdReduction/ShellEnvelopeNonnegativity.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LargeSieve.Bilinear.GcdTailAndMaskedShellBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction
open scoped NumberField Classical

theorem envelope_nonneg
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (M X K : ℝ) (hM : 1 ≤ M) (hX : 1 ≤ X) (hK : 0 < K) :
    0 ≤ B2env F c Q W M X K := by
  unfold B2env
  exact Real.sSup_nonneg' ⟨0, Or.inl (Or.inl rfl), le_rfl⟩

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction

end
