/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/FractionalIdealCharacterExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.WeightedFractionalCharacter
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.PrimeDetermination

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayFractionalCharacterExtension
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    let μ := narrowIdealModulus K m hm
    let P := ClassFieldTheory.rayClassPrimeToIdeals μ
    let F := FractionalIdeal (nonZeroDivisors (𝓞 K)) K
    ∃ f : P →* ℂˣ,
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → I ⊔ m = ⊤ →
        ∀ J : P,
          ((J : ClassFieldTheory.NumberFieldFractionalIdealGroup K) : F) =
            (I : F) →
          (f J : ℂ) = χ I := by
  classical
  let P := ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus K m hm)
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℂˣ :=
    fun v => if h : χ v.asIdeal ≠ 0 then Units.mk0 (χ v.asIdeal) h else 1
  obtain ⟨H, hH⟩ := weightedFractionalCharacter K w
  refine ⟨H.comp P.subtype, ?_⟩
  intro I hI hcop J hJ
  have hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      χ v.asIdeal ≠ 0 →
        (H (ClassFieldTheory.finitePrimeFractionalIdeal v) : ℂ) = χ v.asIdeal := by
    intro v hv
    rw [hH v]
    simp only [w, dif_pos hv, Units.val_mk0]
  have hchi : χ I ≠ 0 := by
    intro h0
    rcases (χ.eq_zero_iff' I).mp h0 with h | h
    · exact hI h
    · exact h hcop
  have hred := rayCharacterIntegralPrimeReduction K m χ H hprime I hchi
    (rayIdealFractionalIdeal K I hI)
    (by rw [rayIdealFractionalIdeal_coe])
  have hJeq : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup K) =
      rayIdealFractionalIdeal K I hI := by
    apply Units.ext
    rw [rayIdealFractionalIdeal_coe]
    exact hJ
  change (H (J : ClassFieldTheory.NumberFieldFractionalIdealGroup K) : ℂ) = χ I
  rw [hJeq]
  exact hred

end DedekindZetaZeroFree.AbelianQuotient
