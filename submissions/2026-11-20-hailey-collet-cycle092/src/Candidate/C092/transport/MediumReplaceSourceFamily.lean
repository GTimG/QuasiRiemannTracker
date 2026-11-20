/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Source-side detector dictionary for arbitrary natural regular cores.
This does not manufacture any outer BaselineSourceData. -/
import Candidate.C092.transport.LowActualSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckePrimeRay HeckeDetectorZeros CompletedGauss
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcreteTraceCRT ConcretePrimeRowBridge
open OAI.SevenEighths.Cycle61Moment.LowBranch
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_MediumReplaceSourceFamily_1b4ddbbb60829655_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- None is the original punctured ordinary row. Some(theta0,theta) contains
ALL relative sectors and each sector's whole ray family, as in ActualLow. -/
def family {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    {z : O} (F : NaturalRow s.character z) :
    Option (RayQuotient.Characters M H × RayQuotient.Characters M H) → Character :=
  fun label => match label with
    | none => excluded F.character s.puncture
    | some pair => twistedFamily M H hH ((excluded F.character s.puncture).product
        (relativeCharacter M H hH η₀ pair.1).inverse.inverse) pair.2

/-- The actual initialKeep/nonexceptional gate implies every character in
the union is nonprincipal; no exclusion of new rows or substitute L-function. -/
theorem family_nonprincipal {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    {z : O} (hz : s.radial.keep z) (F : NaturalRow s.character z) :
    ∀ label,(family M H hH s η₀ F label).residue ≠ 1 := by
  intro label
  cases label with
  | none =>
    have hn := F.nonprincipal (s.row_ne_zero z hz) s.fixedModulus s.puncture
      s.puncture_ne_zero (s.nonexceptional z hz)
    intro hp
    exact hn ((HeckeFiniteDeletion.principal_iff_of_mask (excluded F.character s.puncture) F.character
      (excludePrimes_mask F.character (primeSupport s.puncture)
        (support_prime s.puncture))).mp hp)
  | some pair =>
    exact whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ pair.1).inverse hQM
      (relativeCharacter_fixedQ M H hH η₀ pair.1 s.fixedModulus hQM hQη) z hz F pair.2

/-- Arbitrarily small positive conductor collar, uniform in all later states
and row choices. Fixed character/ray constants enter only the eventual scale.
The collar must be retained: radius U^V alone is not a conductor U^V bound. -/
theorem family_conductor_eventually (η₀ : Character) (bΦ Mcap Bmask margin : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ ∀ s : NaturalState Z Bmask bΦ,
      s.width ≤ Mcap → ∀ (z : O) (F : NaturalRow s.character z),
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ label,((family M H hH s η₀ F label).modulus.absNorm : ℝ) ≤
        Z^(Mcap+Bmask+margin) := by
  let C : ℝ := (fixedConductorFactor : ℝ)*bΦ
  have hf : ∀ᶠ Z : ℝ in atTop,C ≤ Z^margin :=
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop C)
  filter_upwards [eventual_relative_conductor M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin,hf]
    with Z hZ hC
  refine ⟨hZ.1,?_⟩
  intro s hs z F hΦ label
  cases label with
  | some pair => exact hZ.2 s hs z F hΦ pair.1 pair.2
  | none =>
    have hZp : 0 < Z := zero_lt_one.trans hZ.1
    have hn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ*Z^s.rowWidth := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
      exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
    have hFn := F.modulus_power_bound Z s.characterWidth s.rowWidth bΦ hZp hbΦ s.modulus_bound hn
    have hw : Z^(s.characterWidth+s.rowWidth) ≤ Z^Mcap :=
      Real.rpow_le_rpow_of_exponent_le hZ.1.le (by simpa [NaturalState.width,add_comm] using hs)
    change ((excluded F.character s.puncture).modulus.absNorm : ℝ) ≤ _
    rw [excluded_conductor _ _ s.puncture_ne_zero,Nat.cast_mul]
    calc
      _ ≤ ((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask :=
        mul_le_mul (hFn.trans (mul_le_mul_of_nonneg_left hw (by positivity)))
          s.radical_bound (Nat.cast_nonneg _) (by positivity)
      _ = C*Z^(Mcap+Bmask) := by dsimp [C];rw [Real.rpow_add hZp];ring
      _ ≤ Z^margin*Z^(Mcap+Bmask) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
      _ = Z^(Mcap+Bmask+margin) := by rw [←Real.rpow_add hZp];congr 1;ring

/-- Each ActualLow relative family is a literal subfamily of this dictionary.
Thus the union's next-height gate implies the unchanged ActualLow gate. -/
theorem actualLow_of_family_band {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : s.radial.keep z) (a e T : ℝ)
    (hΦ : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0)
    (hband : zeroMaximum (family M H hH s η₀ (naturalRow s.character z (s.row_ne_zero z hz)))
      (family_nonprincipal M H hH s η₀ hQM hQη hz _) T < a+2*e) :
    ActualLow M H hH s η₀ hQM hQη a e T z := by
  refine ⟨hΦ,?_⟩
  intro hz' θ₀
  apply lt_of_le_of_lt (zeroMaximum_subfamily _ _ _ _ (fun θ => some (θ₀,θ)) (fun _ => rfl) T) hband

end QRH.Cycle092.MediumReplace.Source
#print axioms QRH.Cycle092.MediumReplace.Source.family_nonprincipal
#print axioms QRH.Cycle092.MediumReplace.Source.family_conductor_eventually
#print axioms QRH.Cycle092.MediumReplace.Source.actualLow_of_family_band
