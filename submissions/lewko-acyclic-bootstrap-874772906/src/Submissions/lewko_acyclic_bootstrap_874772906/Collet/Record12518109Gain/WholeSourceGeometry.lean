import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeFamilyZeros
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualBinSource

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot CenteredMomentDetectorEnergyInitialState
open HeckePrimeRay HeckeDetectorFamilyInclusion HeckeDetectorZeros Cycle61Moment.LowBranch
open Cycle61Moment Record12518109Natural Record12518109GainActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem whole_natural_coefficients (η η₀ : Character) (u : O) (hu : u≠0)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ (naturalRow η u hu).character j) I=
      idealCoeff (naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character I := by
  have hc (χ : Character) (I : Ideal O) : idealCoeff (excluded χ 1) I=idealCoeff χ I := by
    rw [excluded_ideal χ 1 one_ne_zero,if_pos isCoprime_one_right]
  have he := whole_source_family_mask M H hH η₀ η (naturalRow η u hu).character u hu
    (naturalRow η u hu) 1 one_ne_zero (fun I=>(hc _ I).symm)
    (fun j=>naturalRow (wholeSourceBase M H hH η₀ η j) u hu) j I
  simpa only [hc] using he

theorem whole_natural_nonprincipal (η η₀ : Character) (u : O) (hu : u≠0)
    (hn : ∀j,(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character.residue≠1) :
    ∀j,(wholeSourceFamily M H hH η₀ (naturalRow η u hu).character j).residue≠1 := by
  intro j hp
  exact hn j ((HeckeFiniteDeletion.principal_iff_of_mask _ _
    (coefficient_equality_mask _ _ (whole_natural_coefficients M H hH η η₀ u hu j))).mp hp)

theorem whole_natural_maximum (η η₀ : Character) (u : O) (hu : u≠0)
    (hn : ∀j,(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character.residue≠1) (T : ℝ) :
    zeroMaximum (wholeSourceFamily M H hH η₀ (naturalRow η u hu).character)
      (whole_natural_nonprincipal M H hH η η₀ u hu hn) T=
    zeroMaximum (fun j=>(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character) hn T := by
  exact zeroMaximum_eq_of_mask _ _ _ hn T
    (fun j=>coefficient_equality_mask _ _ (whole_natural_coefficients M H hH η η₀ u hu j))

def relativeRayBase (η η₀ : Character) (u : O) (hu : u≠0)
    (θ : RayQuotient.Characters M H) : Character :=
  (naturalRow η u hu).character.product (relativeCharacter M H hH η₀ θ).inverse.inverse

theorem relative_ray_nonprincipal (η η₀ : Character) (u : O) (hu : u≠0)
    (hn : ∀j,(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character.residue≠1)
    (θ : RayQuotient.Characters M H) :
    ∀θ',(twistedFamily M H hH (relativeRayBase M H hH η η₀ u hu θ) θ').residue≠1 :=
  fun θ'=>whole_natural_nonprincipal M H hH η η₀ u hu hn (.inr (θ,θ'))

theorem relative_ray_maximum_le (η η₀ : Character) (u : O) (hu : u≠0)
    (hn : ∀j,(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character.residue≠1)
    (θ : RayQuotient.Characters M H) (T : ℝ) :
    zeroMaximum (twistedFamily M H hH (relativeRayBase M H hH η η₀ u hu θ))
      (relative_ray_nonprincipal M H hH η η₀ u hu hn θ) T≤
    zeroMaximum (fun j=>(naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character) hn T := by
  rw [←whole_natural_maximum M H hH η η₀ u hu hn T]
  exact zeroMaximum_subfamily
    (twistedFamily M H hH (relativeRayBase M H hH η η₀ u hu θ))
    (wholeSourceFamily M H hH η₀ (naturalRow η u hu).character)
    (relative_ray_nonprincipal M H hH η η₀ u hu hn θ)
    (whole_natural_nonprincipal M H hH η η₀ u hu hn)
    (fun θ'=>Sum.inr (θ,θ')) (fun _=>rfl) T

/-- Exact same amplitude and both source heights, with the real square-root
normalization converted to the original ray-prime polynomial. -/
theorem natural_relative_slot_eq_ray (η η₀ : Character) (u : O) (hu : u≠0)
    (θ : RayQuotient.Characters M H) (W : ℝ→ℂ) (b P σ freq : ℝ) (hP : 0<P) :
    naturalSlot (naturalRow η u hu).character (primePool M H b P)
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
        HeckePrimeAnnular.annularWeight W P σ freq I) P=
    rayPrimePolynomial M H (relativeRayBase M H hH η η₀ u hu θ) W b P σ freq := by
  unfold naturalSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow P hP]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [relativeRayBase,idealCoeff_product,idealCoeff_inverse_conj,map_map,
    Complex.conj_conj]
  ring

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
