/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/Cubic/ArithmeticInducingData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPActualScalarBinding

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

abbrev ActualKPBinding := KPExceptionalRaw.RawFiniteInducingData F ζ hζ q

end
end DedekindZetaZeroFree.KPActualScalarBinding
