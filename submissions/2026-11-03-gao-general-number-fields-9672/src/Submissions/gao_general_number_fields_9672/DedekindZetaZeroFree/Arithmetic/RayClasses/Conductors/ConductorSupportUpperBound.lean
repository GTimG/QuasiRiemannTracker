/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Conductors/ConductorSupportUpperBound.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.QuadraticExtensionRealization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteUnramified

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField Classical
open IsDedekindDomain

theorem conductor_support_upper
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) (d : QuadraticRayExtensionData η)
    (c : ClassFieldTheory.RayClassModulus F)
    (hc : ClassFieldTheory.IsAbelianConductor F d.extension c) :
    ∀ p : HeightOneSpectrum (𝓞 F),
      p ∈ c.finitePart.support → p.asIdeal ⊔ f ≠ ⊤ := by
  intro p hp htop
  exact (Finsupp.mem_support_iff.mp hp)
    ((hc.finiteExponent_eq_zero_iff_unramified p).mpr
      (fun W hW => (d.unramified p htop) W.asIdeal W.isPrime hW))

end DedekindZetaZeroFree.LargeSieve.RootNumber
