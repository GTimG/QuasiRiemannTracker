import Candidate.Cycle63.Moment.WholeSourceFamily
import Candidate.Cycle63.Moment.LowBranch.Conductor

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open LowBranch
open ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem eventual_whole_source_conductor (η₀ : Character) (bΦ Mcap Bmask margin : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ s : NaturalState Z Bmask bΦ,
      s.width ≤ Mcap → ∀ z : O, ∀ F : NaturalRow s.character z,
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ j : WholeSourceIndex M H,
      ((wholeSourceFamily M H hH η₀ (excluded F.character s.puncture) j).modulus.absNorm : ℝ)
        ≤ Z^(Mcap+Bmask+margin) := by
  have hrelative := eventual_relative_conductor M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin
  have hfixed : ∀ᶠ Z : ℝ in atTop, (fixedConductorFactor : ℝ)*bΦ ≤ Z^margin :=
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hrelative,hfixed] with Z hrel hfixed
  refine ⟨hrel.1,?_⟩
  intro s hwidth z F hs j
  cases j with
  | inr j => exact hrel.2 s hwidth z F hs j.1 j.2
  | inl j =>
    change ((excluded F.character s.puncture).modulus.absNorm : ℝ) ≤ _
    have hZp : 0 < Z := zero_lt_one.trans hrel.1
    have hn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ*Z^s.rowWidth := by
      rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
      exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hs)
    have hF := F.modulus_power_bound Z s.characterWidth s.rowWidth bΦ hZp hbΦ
      s.modulus_bound hn
    have hw : Z^(s.characterWidth+s.rowWidth) ≤ Z^Mcap :=
      Real.rpow_le_rpow_of_exponent_le hrel.1.le
        (by simpa only [NaturalState.width,add_comm] using hwidth)
    have hFn : (F.character.modulus.absNorm : ℝ) ≤
        (fixedConductorFactor : ℝ)*bΦ*Z^Mcap :=
      hF.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    rw [excluded_conductor _ _ s.puncture_ne_zero, Nat.cast_mul]
    calc
      _ ≤ ((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask :=
        mul_le_mul hFn s.radical_bound (Nat.cast_nonneg _) (by positivity)
      _ = ((fixedConductorFactor : ℝ)*bΦ)*Z^(Mcap+Bmask) := by
        rw [Real.rpow_add hZp]
        ring
      _ ≤ Z^margin*Z^(Mcap+Bmask) :=
        mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hZp.le _)
      _ = Z^(Mcap+Bmask+margin) := by
        rw [← Real.rpow_add hZp]
        congr 1
        ring

end
end OAI.SevenEighths.Cycle63Moment
