/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/QuadraticFamilies/UniformNormalizationData.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CoreNormalizationData

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

structure AllIndexNormalizedFamilyData {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    extends NormalizedFamilyData Q where
  original_ne_bot : c ≠ ⊥
  all_conductor_dvd : ∀ a, Squarefree a → a ⊔ c = ⊤ → Q.cond a ∣ a * bad
  all_index_dvd : ∀ a, Squarefree a → a ⊔ c = ⊤ → a ∣ Q.cond a * bad

end DedekindZetaZeroFree.LargeSieve.Sieve
