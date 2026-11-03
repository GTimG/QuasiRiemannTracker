/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Torus/GlobalInduction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusInducingPlan
noncomputable section
set_option autoImplicit false
attribute [local instance] KPGlobalProductPolarizationCharacter.localCoverTopology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ModelData := KPGlobalTorusPeriodizationInverse.ModelData F ζ hζ

local instance torusTop (H : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    TopologicalSpace (KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ H) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ H

local instance compactTop (H : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (K : Subgroup (KPGlobalTorusFunctionData.G F ζ hζ)) :
    TopologicalSpace (KPGlobalTorusBorelTwistCompatibility.CompactLevel F ζ hζ H J K) :=
  KPGlobalTorusBorelTwistCompatibility.compactLevelTopology F ζ hζ H J K

end
end DedekindZetaZeroFree.KPGlobalTorusInducingPlan
