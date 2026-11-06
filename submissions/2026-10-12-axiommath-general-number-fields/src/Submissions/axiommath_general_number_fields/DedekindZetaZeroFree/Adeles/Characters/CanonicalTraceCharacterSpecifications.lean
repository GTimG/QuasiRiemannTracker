/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/CanonicalTraceCharacterSpecifications.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductor
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Lattices.CompactOpenLevelLattices
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Characters.TracePairingNondegeneracy
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Characters.RationalTracePullback

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

instance instFactPrimeTraceCharacterSpecNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

end DedekindZetaZeroFree

end
