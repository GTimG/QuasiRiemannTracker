/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Tate/UnitShellFourierIntegrability.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Tate.Local.AnnularFourierMellin
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalSchwartzInversion

@[expose] public section

noncomputable section

open scoped NumberField Classical

open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

variable (F : Type) [Field F] [NumberField F]

instance unitShellFourierAdicCompletionMeasurableSpace (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

instance unitShellFourierAdicCompletionBorelSpace (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

end DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

end
