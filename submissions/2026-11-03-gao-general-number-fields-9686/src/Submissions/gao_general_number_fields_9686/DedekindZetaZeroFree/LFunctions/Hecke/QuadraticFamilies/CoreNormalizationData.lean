/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/QuadraticFamilies/CoreNormalizationData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

structure NormalizedFamilyData {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) where
  bad : Ideal (𝓞 F)
  bad_ne_bot : bad ≠ ⊥
  original_dvd_bad : c ∣ bad
  index_dvd_conductor : ∀ a, Squarefree a → a ⊔ bad = ⊤ → a ∣ Q.cond a
  conductor_dvd_index_bad : ∀ a, Squarefree a → a ⊔ bad = ⊤ → Q.cond a ∣ a * bad

end DedekindZetaZeroFree.LargeSieve.Sieve
