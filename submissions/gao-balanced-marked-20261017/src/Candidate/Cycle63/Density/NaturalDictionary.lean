import Candidate.Cycle63.Density.ActualMoments
import Candidate.LocalMoment.HeightUniformDensity

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeDetectorZeros HeckeDetectorFamilyInclusion
open CenteredMomentNaturalRowSource
open ConcretePrimeRowBridge CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O

theorem coefficient_equality_mask (χ ψ : Character)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) :
    ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · simpa only [hc, ite_true] using hcoeff I
  · rw [ite_eq_right hc]
    by_contra hn
    exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn).2

def FixedUnmarkedDictionary.naturalFamily {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) : Label → Character :=
  fun j => (naturalRow (D.base j) u.val u.property.1).character

theorem FixedUnmarkedDictionary.natural_coefficients {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) (j : Label) (I : Ideal O) :
    idealCoeff (D.naturalFamily u j) I =
      idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I :=
  natural_row_moment_dictionary (D.base j) u I

/-- A conductor bound for the actual natural representative, independent of scale. -/
theorem FixedUnmarkedDictionary.natural_conductor_bound {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ u : FreeRow, ∀ j,
      ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤ K * rowNorm u := by
  let K : ℝ := 1 + ∑ j, ((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)
  have hs : 0 ≤ ∑ j, ((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro u j
  have hc : ((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) ≤ K := by
    have hh := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => (by positivity :
        0 ≤ ((D.base k).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)))
      (Finset.mem_univ j)
    dsimp [K]
    linarith
  have hb : ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤
      (((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)) * rowNorm u := by
    change ((naturalRow (D.base j) u.val u.property.1).character.modulus.absNorm : ℝ) ≤
      (((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)) *
        ((Ideal.span {u.val}).absNorm : ℝ)
    exact_mod_cast (naturalRow (D.base j) u.val u.property.1).natural_modulus_bound
  exact hb.trans (mul_le_mul_of_nonneg_right hc (rowNorm_ge_one u |>.trans' zero_le_one))

theorem FixedUnmarkedDictionary.natural_nonprincipal {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow)
    (hu : ∀ j, ((D.data j).character ⟨u.val, u.property.1⟩).residue ≠ 1) :
    ∀ j, (D.naturalFamily u j).residue ≠ 1 := by
  intro j hp
  exact hu j ((principal_iff_of_mask _ _
    (coefficient_equality_mask _ _ (D.natural_coefficients u j))).mp hp)

theorem FixedUnmarkedDictionary.natural_maximum {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (u : FreeRow)
    (hu : ∀ j, ((D.data j).character ⟨u.val, u.property.1⟩).residue ≠ 1) (T : ℝ) :
    zeroMaximum (D.naturalFamily u) (D.natural_nonprincipal u hu) T =
      zeroMaximum (fun j => (D.data j).character ⟨u.val, u.property.1⟩) hu T :=
  zeroMaximum_eq_of_mask _ _ _ hu T
    (fun j => coefficient_equality_mask _ _ (D.natural_coefficients u j))

/-- Whole-character conjugation retains the natural modulus and reflects the zero heights. -/
theorem FixedUnmarkedDictionary.oriented_natural {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) (j : Label) (reverse : Bool) :
    let χ := if reverse then (D.naturalFamily u j).inverse else D.naturalFamily u j
    χ.modulus = (D.naturalFamily u j).modulus ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if reverse then starRingEnd ℂ (idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I)
        else idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I := by
  cases reverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨trivial, D.natural_coefficients u j⟩
  · refine ⟨rfl, ?_⟩
    intro I
    rw [idealCoeff_inverse_conj, D.natural_coefficients]

/-- Only free cores form this finite exceptional population. Their raw
sixth-power multiples are handled by convolution, never declared finite. -/
theorem FixedUnmarkedDictionary.exceptional_cores_finite {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) :
    {u : FreeRow | ∃ j, ¬initialKeep
      (D.base j) (D.fixedIdeal j) u.val}.Finite := by
  have h : (⋃ j, {u : FreeRow | ¬initialKeep (D.base j) (D.fixedIdeal j) u.val}).Finite := by
    apply Set.finite_iUnion
    intro j
    exact fixed_exceptional_free_finite (D.base j) (D.fixedIdeal j) (D.nonzero j)
      (D.proper j) (D.divides72 j) (D.dividesBase j)
  simpa only [Set.iUnion_ofPred] using h

def FixedUnmarkedDictionary.exceptionalCore {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) : Prop :=
  ∃ j, ¬initialKeep (D.base j) (D.fixedIdeal j) u.val

theorem FixedUnmarkedDictionary.regular_nonprincipal {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) (hu : ¬D.exceptionalCore u) :
    ∀ j, ((D.data j).character ⟨u.val, u.property.1⟩).residue ≠ 1 := by
  intro j hp
  have hkeep : initialKeep (D.base j) (D.fixedIdeal j) u.val := by
    by_contra hn
    exact hu ⟨j, hn⟩
  have hn : (D.naturalFamily u j).residue ≠ 1 :=
    (naturalRow (D.base j) u.val u.property.1).nonprincipal u.property.1
      (D.fixedIdeal j) 1 one_ne_zero hkeep.2
  exact hn ((principal_iff_of_mask _ _
    (coefficient_equality_mask _ _ (D.natural_coefficients u j))).mpr hp)

#print axioms FixedUnmarkedDictionary.natural_conductor_bound
#print axioms FixedUnmarkedDictionary.exceptional_cores_finite
end SevenEighths.LocalMoment
end
end OAI
