/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/StandardResidueTraceCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Characters.StandardAdditiveCharacter
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.PrincipalMellinSource.ProfileCore.FixedSupport

variable {F : Type} [Field F] [NumberField F]

abbrev StandardResidue (p : KPFinitePlace F) :=
  IsLocalRing.ResidueField (p.adicCompletionIntegers F)

def standardReduction (p : KPFinitePlace F) :
    p.adicCompletionIntegers F →+* StandardResidue p := IsLocalRing.residue _

def standardResidueFieldEquiv (p : KPFinitePlace F) :
    StandardResidue p ≃+* (𝓞 F ⧸ p.asIdeal) :=
  (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField p).symm

instance standardResidueFinite (p : KPFinitePlace F) : Finite (StandardResidue p) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot p.asIdeal p.ne_bot
  exact Finite.of_equiv (𝓞 F ⧸ p.asIdeal) (standardResidueFieldEquiv p).symm.toEquiv

end DedekindZetaZeroFree.PrincipalMellinSource.ProfileCore.FixedSupport

end
