/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/PrimeArtinValues.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

abbrev ComplexDual (G : Type*) [Group G] := G →* ℂˣ

noncomputable instance instFintypeComplexDual (G : Type*) [CommGroup G] [Finite G] :
    Fintype (ComplexDual G) := by
  letI : Fintype G := Fintype.ofFinite G
  exact Fintype.ofEquiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.toEquiv.symm

noncomputable def primeArtinValue
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (ρ : ComplexDual (L ≃ₐ[K] L))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ℂ := by
  classical
  exact if Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker then
    (ρ (ClassFieldTheory.arithmeticFrobeniusAt (K := K) W) : ℂ) else 0

end DedekindZetaZeroFree.AbelianQuotient
