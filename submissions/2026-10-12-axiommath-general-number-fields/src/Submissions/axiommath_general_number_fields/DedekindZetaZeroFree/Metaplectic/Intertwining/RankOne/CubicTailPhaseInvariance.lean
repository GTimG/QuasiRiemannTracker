/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/CubicTailPhaseInvariance.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailBruhatIdentity
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.SignedWeylInversion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

theorem actual_tail_phase_cube (u v : (LocalField F q)ˣ) :
    actualTailPhase F ζ hζ q (u ^ 3 * v) = actualTailPhase F ζ hζ q v := by

  simp only [actualTailPhase,
    DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.kappa_eq_one]

end DedekindZetaZeroFree.KPRankOneShellRepair

end
