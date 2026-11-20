/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/RankTwoLattices/DeterminantAndLineClasses.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.DeterminantIdealCalculus
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.LineAdaptedIdealDecomposition
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

def determinantIdeal
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) : FractionalIdeal R⁰ K :=
  ⟨determinantSubmodule R K M.val,
    kp_cusp_determinantSubmodule_isFractional R K M⟩

def coefficientIdeal
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (v : K × K) (hv : v ≠ 0) : FractionalIdeal R⁰ K :=
  ⟨coefficientSubmodule R K M.val v,
    kp_cusp_coefficientSubmodule_isFractional R K M v hv⟩

noncomputable def determinantClass
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) : ClassGroup R :=
  ClassGroup.mk K (Units.mk0 (determinantIdeal R K M) (by
    intro h
    apply kp_cusp_determinantSubmodule_ne_bot R K M
    exact (congrArg Subtype.val h).trans FractionalIdeal.coe_zero))

noncomputable def lineClass
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) (q : RationalLine K) : ClassGroup R :=
  ClassGroup.mk K (Units.mk0 (coefficientIdeal R K M q.rep q.rep_nonzero) (by
    intro h
    apply kp_cusp_coefficientSubmodule_ne_bot R K M q.rep q.rep_nonzero
    exact (congrArg Subtype.val h).trans FractionalIdeal.coe_zero))

end DedekindZetaZeroFree
