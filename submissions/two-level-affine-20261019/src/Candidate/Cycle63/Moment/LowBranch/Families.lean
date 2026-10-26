import Candidate.Cycle63.Arithmetic.Constants
import Candidate.LocalMoment.RestrictedIncumbent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckePrimeRay HeckeDetectorZeros ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentFixedRayInducingTransport
open CenteredMomentRayNonprincipal
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- All ray twists of the actual punctured natural relative character remain
nonprincipal. The exclusion is the state's actual fixed ideal. -/
theorem whole_nonprincipal {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (ν : Character) (hQM : s.fixedModulus ≤ M) (hQν : s.fixedModulus ≤ ν.modulus)
    (z : O) (hz : s.radial.keep z) (F : NaturalRow s.character z) :
    ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ((excluded F.character s.puncture).product ν.inverse)
        θ).residue ≠ 1 := by
  have hmask : s.mask ≠ 0 := mul_ne_zero fixedBadMask_ne_zero
    (idealGenerator_ne_zero _ s.puncture_ne_zero)
  have hex := (not_fixedInducingRow_product_inverse_iff s.character ν s.fixedModulus
    s.mask 1 z hQν hmask one_ne_zero (s.row_ne_zero z hz)
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))).mpr (s.nonexceptional z hz)
  apply all_ray_twists_nonprincipal M H hH (s.character.product ν.inverse)
    ((excluded F.character s.puncture).product ν.inverse) s.fixedModulus s.mask 1 z
    _ hQM hex
  simpa only [one_mul] using product_row_presentation s.character
    (excluded F.character s.puncture) ν.inverse s.mask 1 z
    (by simpa only [one_mul, NaturalState.mask] using F.masked_element _ s.puncture_ne_zero)

/-- A subfamily maximum is bounded by the genuine finite whole-family maximum,
including the sentinel at 51/100. No selected-zero surrogate is used. -/
theorem zeroMaximum_subfamily {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (χ : ι → Character) (ψ : ρ → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ j, (ψ j).residue ≠ 1)
    (f : ι → ρ) (hf : ∀ i, χ i = ψ (f i)) (T : ℝ) :
    zeroMaximum χ hχ T ≤ zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with h | h
  · obtain ⟨i,z,hzero,hheight,he⟩ := maximum_attained χ hχ T h
    have hb := zero_re_le_maximum ψ hψ T (f i) (by rw [he]; exact h.le)
      hheight (by rwa [← hf])
    simpa only [he] using hb
  · exact h.trans (zeroMaximum_bounds ψ hψ T).1

/-- A literal buffered gate implies the low exponent; a bin below `(1+q)/2` has `2*a-1 ≤ q`. -/
theorem low_rate {q a : ℝ} (ha : a ≤ (1+q)/2) : 2*a-1 ≤ q := by
  linarith

end
end OAI.SevenEighths.Cycle63Moment.LowBranch
