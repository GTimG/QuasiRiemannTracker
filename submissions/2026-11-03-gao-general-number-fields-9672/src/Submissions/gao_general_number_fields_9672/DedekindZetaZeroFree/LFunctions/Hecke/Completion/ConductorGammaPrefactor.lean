/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/Completion/ConductorGammaPrefactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

noncomputable def normalizedHeckePrefactor (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F

end DedekindZetaZeroFree.Hecke
