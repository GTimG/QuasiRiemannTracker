/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/ResiduePhases/GlobalQuotientCompatibility.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.GlobalCongruence
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacters.GlobalCompatibility

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.CompatiblePrimeRawLocal
open LocalFiniteSums CRTRawLocalModel
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem psi_residueMap_eq_negativeTrace (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    psi C p n (residueMap C p n x) =
      (negativeTrace p (algebraMap F (LocalField p) (x : F) / uniformizer C p ^ n) : ℂ) := by

  rw [psi]
  exact congrArg (fun z : Circle => (z : ℂ))
    (LocalFiniteSumCompatibility.quotientTrace_mk C p n x)

theorem canonicalNumeratorCongruence_iff (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (d : Residue C p k) :
    numeratorCongruence C p t k J 1 1 (canonicalLocalRepresentative C p k d) ↔
      residueMap C p k (generator C p ^ J) =
        residueMap C p k (generator C p ^ t) * d := by
  have hh := CongruenceBridgeRace.congruent_iff_residue C p k
    (generator C p ^ J) (generator C p ^ t * (lifts C p k).val d)
  have hd : residueMap C p k ((lifts C p k).val d) = d :=
    (lifts C p k).property d
  simpa [numeratorCongruence, canonicalLocalRepresentative, uniformizer, hd] using hh

end DedekindZetaZeroFree.CompatiblePrimeRawLocal

end
