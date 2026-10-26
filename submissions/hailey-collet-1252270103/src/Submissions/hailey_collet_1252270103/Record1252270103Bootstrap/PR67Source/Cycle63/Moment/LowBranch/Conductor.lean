import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.LocalMoment.RestrictedIncumbent
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators HeckeNotation
open ConcreteTraceCRT CenteredMomentAllocatedNaturalSource
open Filter HeckeFamily HeckePrimeRay ConcretePrimeRowBridge CompletedGauss
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual common puncture contributes its radical, with no conductor
renaming or removal of Euler factors. -/
theorem excluded_conductor (χ : Character) (R : Ideal O) (hR : R ≠ 0) :
    (excluded χ R).modulus.absNorm = χ.modulus.absNorm*R.radical.absNorm := by
  change (χ.modulus*(∏ P ∈ primeSupport R, P)).absNorm = _
  rw [primeSupport_product_radical R hR, map_mul]

/-- A common threshold precedes every natural state, live width and ray label.
Only the actual radial support controls the moving row conductor. -/
theorem eventual_relative_conductor (η₀ : Character) (bΦ Mcap Bmask margin : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ s : NaturalState Z Bmask bΦ,
      s.width ≤ Mcap → ∀ z : O, ∀ F : NaturalRow s.character z,
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ θ₀ θ : RayQuotient.Characters M H,
      ((twistedFamily M H hH ((excluded F.character s.puncture).product
        (relativeCharacter M H hH η₀ θ₀).inverse.inverse) θ).modulus.absNorm : ℝ)
        ≤ Z^(Mcap+Bmask+margin) := by
  let C : ℝ := (fixedConductorFactor : ℝ)*bΦ*
    ((M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ))*(M.absNorm : ℝ)
  have hfixed : ∀ᶠ Z : ℝ in atTop, C ≤ Z^margin :=
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop C)
  filter_upwards [hfixed, eventually_gt_atTop (1:ℝ)] with Z hC hZ
  refine ⟨hZ,?_⟩
  intro s hs z F hΦ θ₀ θ
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ*Z^s.rowWidth := by
    rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have hF := F.modulus_power_bound Z s.characterWidth s.rowWidth bΦ hZp hbΦ
    s.modulus_bound hn
  have hwidth : Z^(s.characterWidth+s.rowWidth) ≤ Z^Mcap :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by simpa [NaturalState.width,add_comm] using hs)
  have hFn : (F.character.modulus.absNorm : ℝ) ≤
      (fixedConductorFactor : ℝ)*bΦ*Z^Mcap :=
    hF.trans (mul_le_mul_of_nonneg_left hwidth (by positivity))
  have hν : (((relativeCharacter M H hH η₀ θ₀).inverse.inverse).modulus.absNorm : ℝ)
      ≤ (M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ) := by
    exact_mod_cast relativeCharacter_modulus M H hH η₀ θ₀
  have hp := HeckePrimeScale.product_modulus_bound (excluded F.character s.puncture)
    (relativeCharacter M H hH η₀ θ₀).inverse.inverse
  have ht := HeckePrimeScale.twisted_modulus_bound M H hH
    ((excluded F.character s.puncture).product (relativeCharacter M H hH η₀ θ₀).inverse.inverse) θ
  have he : ((excluded F.character s.puncture).modulus.absNorm : ℝ) ≤
      ((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask := by
    rw [excluded_conductor _ _ s.puncture_ne_zero, Nat.cast_mul]
    exact mul_le_mul hFn s.radical_bound (Nat.cast_nonneg _) (by positivity)
  have hp' : (((excluded F.character s.puncture).product
      (relativeCharacter M H hH η₀ θ₀).inverse.inverse).modulus.absNorm : ℝ) ≤
      (((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask)*
        ((M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ)) := by
    exact (show _ ≤ _ by exact_mod_cast hp).trans
      (mul_le_mul he hν (Nat.cast_nonneg _) (by positivity))
  have ht' : ((twistedFamily M H hH ((excluded F.character s.puncture).product
      (relativeCharacter M H hH η₀ θ₀).inverse.inverse) θ).modulus.absNorm : ℝ) ≤
      (((excluded F.character s.puncture).product (relativeCharacter M H hH η₀ θ₀).inverse.inverse).modulus.absNorm : ℝ)*(M.absNorm : ℝ) := by exact_mod_cast ht
  apply ht'.trans
  calc
    _ ≤ ((((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask)*
        ((M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ)))*(M.absNorm : ℝ) :=
      mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg _)
    _ = C*Z^(Mcap+Bmask) := by dsimp [C]; rw [Real.rpow_add hZp]; ring
    _ ≤ Z^margin*Z^(Mcap+Bmask) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(Mcap+Bmask+margin) := by
      rw [← Real.rpow_add hZp]
      congr 1
      ring

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
