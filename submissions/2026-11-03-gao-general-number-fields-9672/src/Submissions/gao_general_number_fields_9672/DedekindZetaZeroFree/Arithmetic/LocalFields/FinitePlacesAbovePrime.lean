/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/FinitePlacesAbovePrime.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.All

@[expose] public section

set_option autoImplicit false

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped NumberField

abbrev FinitePlacesAbove (K : Type*) (L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 K)) :=
  {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = w}

noncomputable def finitePlacesAboveFintype (K : Type*) (L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : HeightOneSpectrum (𝓞 K)) :
    Fintype (FinitePlacesAbove K L w) := by
  letI := AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
    (K := K) (L := L) (HeightOneSpectrum.adicAbv K w)
    (RayClass.adicAbv_isNontrivial w)
  exact Fintype.ofEquiv _ (finitePlaceExtensionEquivAbove (K := K) (L := L) w)

noncomputable def finitePlacesAboveRationalPrimeFintype (L : Type*)
    [Field L] [NumberField L] (p : Nat.Primes) :
    Fintype (FinitePlacesAbove ℚ L (Rat.HeightOneSpectrum.primesEquiv.symm p)) :=
  finitePlacesAboveFintype ℚ L (Rat.HeightOneSpectrum.primesEquiv.symm p)

end DedekindZetaZeroFree
