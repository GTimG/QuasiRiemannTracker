import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeRegularSetup

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open HeckeFiniteDeletion HeckeDetectorZeros
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open Cycle61Moment Record12518109Natural Record12518109GainWholeZeros Record12518109GainDeletion
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

theorem nonprincipal_of_excluded_coefficients (χ ψ : Character) (R : Ideal O)
    (hc : ∀I,idealCoeff χ I=idealCoeff (excluded ψ R) I) (hn : χ.residue≠1) : ψ.residue≠1 := by
  intro hp
  have hm := coefficient_equality_mask χ (excluded ψ R) hc
  have he := fun I=>excludePrimes_mask ψ _ (support_prime R) I
  exact hn ((principal_iff_of_mask χ (excluded ψ R) hm).mpr
    ((principal_iff_of_mask (excluded ψ R) ψ he).mpr hp))

theorem maximum_eq_of_excluded_coefficients {Label : Type*} [Fintype Label]
    (χ ψ : Label→Character) (R : Label→Ideal O)
    (hχ : ∀j,(χ j).residue≠1) (hψ : ∀j,(ψ j).residue≠1)
    (hc : ∀j I,idealCoeff (χ j) I=idealCoeff (excluded (ψ j) (R j)) I) (T : ℝ) :
    zeroMaximum χ hχ T=zeroMaximum ψ hψ T := by
  have he (j : Label) : (excluded (ψ j) (R j)).residue≠1 := by
    intro hp
    exact hψ j ((principal_iff_of_mask _ _ (fun I=>excludePrimes_mask (ψ j) _ (support_prime (R j)) I)).mp hp)
  exact (zeroMaximum_eq_of_mask χ (fun j=>excluded (ψ j) (R j)) hχ he T
    (fun j=>coefficient_equality_mask _ _ (hc j))).trans
    (zeroMaximum_eq_of_mask _ ψ he hψ T
      (fun j I=>excludePrimes_mask (ψ j) _ (support_prime (R j)) I))

variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem source_root_coefficients (η η₀ χ : Character) (u : FreeRow) (B : NZIdeal)
    (R : Ideal O) (hR : R≠0)
    (hc : ∀I,idealCoeff χ I=idealCoeff (excluded
      (naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property).character R) I)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ χ j) I=
      idealCoeff (excluded (naturalRow (wholeSourceBase M H hH η₀ η j) u.val u.property.1).character (B.val*R)) I := by
  rw [whole_source_family_mask M H hH η₀ η χ (sixthFrequencyEquiv (u,B)).val
    (sixthFrequencyEquiv (u,B)).property (naturalRow η _ _) R hR hc
    (fun k=>naturalRow (wholeSourceBase M H hH η₀ η k) _ _) j I]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have hh := naturalRow_sixth_masked_ideal
    (naturalRow (wholeSourceBase M H hH η₀ η j) u.val u.property.1)
    (ConcretePrimeRowBridge.idealGenerator B.val) hg
    (naturalRow (wholeSourceBase M H hH η₀ η j) (sixthFrequencyEquiv (u,B)).val
      (sixthFrequencyEquiv (u,B)).property) R hR I
  rwa [ConcretePrimeRowBridge.span_idealGenerator] at hh

theorem clean_core_coefficients (η η₀ : Character) (u : FreeRow)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character I=
      idealCoeff (excluded (naturalRow (wholeSourceBase M H hH η₀ η j) u.val u.property.1).character
        (wholeAnchorMask M H hH η₀)) I := by
  dsimp only [cleanWholeBase]
  rw [(naturalRow _ _ _).ideal,whole_base_excluded_coefficients M H hH η η₀ _
    (wholeAnchorMask_ne_zero M H hH η₀) j I,excluded_ideal _ _ (wholeAnchorMask_ne_zero M H hH η₀),
    excluded_ideal _ _ (wholeAnchorMask_ne_zero M H hH η₀),(naturalRow _ _ _).ideal]
  split_ifs <;> simp

/-- The actual buffered source bin is exactly the regular core's buffered
bin. Root masks and moving holes add only nonvanishing finite Euler
factors in positive real part. Both maximum boundaries are preserved. -/
theorem source_root_maximum_eq_clean (η η₀ χ : Character) (u : FreeRow) (B : NZIdeal)
    (R : Ideal O) (hR : R≠0)
    (hc : ∀I,idealCoeff χ I=idealCoeff (excluded
      (naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property).character R) I)
    (hn : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1)
    (hnclean : ∀j,(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character.residue≠1)
    (T : ℝ) :
    zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn T=
    zeroMaximum (fun j=>(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character) hnclean T := by
  let core := fun j=>(naturalRow (wholeSourceBase M H hH η₀ η j) u.val u.property.1).character
  have hcore (j : WholeSourceIndex M H) : (core j).residue≠1 :=
    nonprincipal_of_excluded_coefficients _ _ (B.val*R)
      (source_root_coefficients M H hH η η₀ χ u B R hR hc j) (hn j)
  have h₁ := maximum_eq_of_excluded_coefficients (wholeSourceFamily M H hH η₀ χ) core
    (fun _=>B.val*R) hn hcore (source_root_coefficients M H hH η η₀ χ u B R hR hc) T
  have h₂ := maximum_eq_of_excluded_coefficients
    (fun j=>(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character) core
    (fun _=>wholeAnchorMask M H hH η₀) hnclean hcore (clean_core_coefficients M H hH η η₀ u) T
  exact h₁.trans h₂.symm

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
