/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Conductors/NormConductorFiniteSupport.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FiniteModulusIdealEncoding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

theorem normConductorRayClassModulus_infinitePart
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E] :
    (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus K E).infinitePart =
      Finset.univ := by
  rfl

theorem normConductorFiniteSupport
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E]
    (p : HeightOneSpectrum (𝓞 K)) :
    (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus K E).finitePart p = 0 ↔
      ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver p.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  change
    (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
        (K := K) (L := E)) p = 0 ↔
      ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver p.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
  have hmem :
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := E)) p = 0 ↔
        p ∉ (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := E)).support := by
    rw [Finsupp.mem_support_iff]
    exact not_not.symm
  rw [hmem,
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces,
    mem_ramifiedBaseFinitePlaces_iff]
  simp only [not_exists, not_and, not_not]

theorem narrowIdealModulus_normConductor
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E] :
    let c := ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus K E
    let m := finiteRayModulusIdeal K c.finitePart
    let hm := finiteRayModulusIdeal_ne_bot K c.finitePart
    narrowIdealModulus K m hm = c := by
  intro c m hm
  exact narrowIdealModulus_finiteRayModulusIdeal K c
    (normConductorRayClassModulus_infinitePart K E)

theorem normConductorIdeal_coprime
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E]
    (p : HeightOneSpectrum (𝓞 K)) :
    let c := ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus K E
    let m := finiteRayModulusIdeal K c.finitePart
    p.asIdeal ⊔ m = ⊤ ↔
      ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver p.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  intro c m
  rw [finiteRayModulusIdeal_coprime]
  exact normConductorFiniteSupport K E p

end DedekindZetaZeroFree.AbelianQuotient

end
