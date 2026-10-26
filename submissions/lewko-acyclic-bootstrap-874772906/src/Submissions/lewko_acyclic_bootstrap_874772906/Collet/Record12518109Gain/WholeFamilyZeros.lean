/- Adapted from PR63 Cycle63/Marked/WholeFamilyZeros.lean; Apache-2.0.
Only import and namespace relocation. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.ActualNaturalBatch
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.NaturalMaskTransport

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109GainWholeZeros
noncomputable section
open scoped Classical
open HeckeFamily HeckeFiniteDeletion LocalMoment Record12518109Natural
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion Cycle61Moment
local notation "O" => HeckeFamily.O

theorem positive_zero_excluded (χ : Character) (R : Ideal O) {s : ℂ}
    (hs : 0<s.re) (hpole : s≠1 ∨ χ.residue≠1) (hz : LFunction χ s=0) :
    LFunction (excluded χ R) s=0 ∧ (s≠1 ∨ (excluded χ R).residue≠1) := by
  have hm : ∀ I : Ideal O,idealCoeff (excluded χ R) I=
      if IsCoprime I (excluded χ R).modulus then idealCoeff χ I else 0 :=
    fun I=>excludePrimes_mask χ _ (support_prime R) I
  have hp : s≠1 ∨ (excluded χ R).residue≠1 := by
    rcases hpole with hp | hp
    · exact Or.inl hp
    · exact Or.inr (fun he=>hp ((principal_iff_of_mask _ _ hm).mp he))
  exact ⟨(positive_zeros_eq_of_mask_nonpole _ _ hm hs hp).1.mpr hz,hp⟩

theorem natural_excluded_base_coefficients (η : Character) (R : Ideal O) (hR : R≠0)
    (u : O) (hu : u≠0) (I : Ideal O) :
    idealCoeff (naturalRow (excluded η R) u hu).character I=
      idealCoeff (excluded (naturalRow η u hu).character R) I := by
  rw [(naturalRow (excluded η R) u hu).ideal,excluded_ideal _ _ hR,
    excluded_ideal _ _ hR,(naturalRow η u hu).ideal]
  split_ifs <;> simp

theorem natural_excluded_base_zero (η : Character) (R : Ideal O) (hR : R≠0)
    (u : O) (hu : u≠0) {s : ℂ} (hs : 0<s.re)
    (hpole : s≠1 ∨ (naturalRow η u hu).character.residue≠1)
    (hz : LFunction (naturalRow η u hu).character s=0) :
    LFunction (naturalRow (excluded η R) u hu).character s=0 ∧
      (s≠1 ∨ (naturalRow (excluded η R) u hu).character.residue≠1) := by
  have hp:=positive_zero_excluded _ R hs hpole hz
  have he:=positive_zeros_eq_of_coefficients _ _
    (fun I=>(natural_excluded_base_coefficients η R hR u hu I).symm) hs hp.2
  exact ⟨he.1.mp hp.1,he.2⟩

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem whole_base_excluded_coefficients (η η₀ : Character) (R : Ideal O) (hR : R≠0)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceBase M H hH η₀ (excluded η R) j) I=
      idealCoeff (excluded (wholeSourceBase M H hH η₀ η j) R) I := by
  cases j with
  | inl j=>rfl
  | inr j=>
    change idealCoeff (((excluded η R).product _).product _) I=_
    simp only [idealCoeff_product,excluded_ideal _ _ hR,wholeSourceBase]
    split_ifs <;> simp [idealCoeff_product]

/-- Adding one fixed conductor mask preserves every positive nonpole zero
of the whole source family, with its same finite label and same height. -/
theorem whole_family_clean_zero (η η₀ : Character) (u : O) (hu : u≠0)
    (j : WholeSourceIndex M H) {s : ℂ} (hs : 0<s.re)
    (hpole : s≠1 ∨ (naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character.residue≠1)
    (hz : LFunction (naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character s=0) :
    let base:=excluded η (wholeAnchorMask M H hH η₀)
    LFunction (naturalRow (wholeSourceBase M H hH η₀ base j) u hu).character s=0 ∧
      (s≠1 ∨ (naturalRow (wholeSourceBase M H hH η₀ base j) u hu).character.residue≠1) := by
  intro base
  have hR:=wholeAnchorMask_ne_zero M H hH η₀
  have he : ∀ I : Ideal O,
      idealCoeff (naturalRow (excluded (wholeSourceBase M H hH η₀ η j)
        (wholeAnchorMask M H hH η₀)) u hu).character I=
      idealCoeff (naturalRow (wholeSourceBase M H hH η₀ base j) u hu).character I := by
    intro I
    rw [(naturalRow _ u hu).ideal,(naturalRow _ u hu).ideal]
    rw [whole_base_excluded_coefficients M H hH η η₀ _ hR j I]
  have hp:=natural_excluded_base_zero (wholeSourceBase M H hH η₀ η j) _ hR u hu hs hpole hz
  have hh:=positive_zeros_eq_of_coefficients _ _ he hs hp.2
  exact ⟨hh.1.mp hp.1,hh.2⟩

end
end OAI.SevenEighths.Record12518109GainWholeZeros
#print axioms OAI.SevenEighths.Record12518109GainWholeZeros.whole_family_clean_zero
