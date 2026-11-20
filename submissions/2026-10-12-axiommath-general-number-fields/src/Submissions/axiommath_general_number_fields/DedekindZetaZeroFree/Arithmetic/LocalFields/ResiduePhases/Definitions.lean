/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/ResiduePhases/Definitions.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.PhaseDifference
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacters.SIntegerConductor

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.CRTRawLocalModel
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def Congruent (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x y : LocalField p) : Prop :=
  ∃ r : LocalIntegers p, x - y = uniformizer C p ^ n * (r : LocalField p)

def canonicalLocalRepresentative (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : Residue C p n) : LocalField p :=
  algebraMap F (LocalField p) ((lifts C p n).val x : F)

def numeratorCongruence (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (a h : (LocalIntegers p)ˣ)
    (d : LocalField p) : Prop :=
  Congruent C p k ((h.val : LocalField p) * uniformizer C p ^ J)
    ((a.val : LocalField p) * uniformizer C p ^ t * d)

def rawPhase (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (s a h : (LocalIntegers p)ˣ)
    (d v : LocalField p) : ℂ :=
  (negativeTrace p
    ((((h.val : LocalField p) * uniformizer C p ^ J -
      (a.val : LocalField p) * uniformizer C p ^ t * d) * v) /
      ((s.val : LocalField p) * (a.val : LocalField p) *
        uniformizer C p ^ (k + t))) : ℂ)

end DedekindZetaZeroFree.CRTRawLocalModel

end
