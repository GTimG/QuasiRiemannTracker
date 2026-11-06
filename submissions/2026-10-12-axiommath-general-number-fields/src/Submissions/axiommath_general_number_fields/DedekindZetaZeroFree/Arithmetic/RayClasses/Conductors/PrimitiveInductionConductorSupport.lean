/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Conductors/PrimitiveInductionConductorSupport.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Nonvanishing.Mellin.InitialFrequencyDecomposition
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyTwistsAndLocalCharacters
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveTrivialCharacter

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem target_primitive_inducer
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ η0 : Detector.PrimitiveFrequencyCharacter F,
      Detector.conductorSupportedOn F
        (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) η0 ∧
      (∀ I : R.A.Exterior, η0.character I.val = R.target I.val) ∧
      ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
        I ⊔ (R.A.modulus * η0.conductor) = ⊤ → η0.character I = R.target I := by
  classical
  obtain ⟨χ, hχprinc, hχprim⟩ :=
    PrincipalMu12Pointwise.principal_primitive_top_character_exists F

  have hmod : ∀ I : R.A.Exterior, I.val ⊔ R.A.modulus = ⊤ := by
    intro I
    by_contra h
    obtain ⟨v, hv⟩ := (IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists
      (NumberField.RingOfIntegers.not_isField F) (I.val ⊔ R.A.modulus)).mp h
    have hvSf : v ∈ R.A.Sf := R.A.modulus_support v (le_sup_right.trans hv)
    have hI : I.val ⊔ v.asIdeal = ⊤ :=
      (R.A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hvSf
    have hIv : I.val ≤ v.asIdeal := le_sup_left.trans hv
    exact v.isPrime.ne_top (top_le_iff.mp (hI ▸ sup_le hIv le_rfl))
  refine ⟨⟨⊤, top_ne_bot, χ, hχprim⟩, ?_, ?_, ?_⟩
  · intro v hv
    exact absurd (top_le_iff.mp hv) v.isMaximal.ne_top
  · intro I
    rw [hχprinc I.val I.property.1 (by simp),
      R.probe.principal I.val I.property.1 (hmod I)]
  · intro I hI hsup
    have hsup' : I ⊔ R.A.modulus = ⊤ := by simpa using hsup
    rw [hχprinc I hI (by simp), R.probe.principal I hI hsup']

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
