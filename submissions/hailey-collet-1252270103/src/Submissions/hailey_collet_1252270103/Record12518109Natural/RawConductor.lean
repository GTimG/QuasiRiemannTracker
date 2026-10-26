/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original masked raw relative-ray conductors, uniform over all raw frequencies. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.LowBranch.Conductor
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily HeckePrimeRay HeckeInverseAmplification ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem raw_relative_conductor_bound (η η₀ : Character) :
    ∃K : ℝ,0≤K ∧∀h : NonzeroFrequency,∀R : Ideal O,R≠0→
      ∀θ θ',((twistedFamily M H hH
        ((excluded (naturalRow η h.val h.property).character R).product
          (relativeCharacter M H hH η₀ θ).inverse.inverse) θ').modulus.absNorm:ℝ)≤
        K*rawFrequencyNorm h*(R.absNorm:ℝ) := by
  let A : ℝ := (η.modulus.absNorm:ℝ)*(fixedConductorFactor:ℝ)
  let B : ℝ := (M.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ)
  let K : ℝ := A*B*(M.absNorm:ℝ)
  refine ⟨K,by dsimp [K,A,B];positivity,?_⟩
  intro h R hR θ θ'
  have hF : ((naturalRow η h.val h.property).character.modulus.absNorm:ℝ)≤A*rawFrequencyNorm h := by
    dsimp only [A,rawFrequencyNorm]
    exact_mod_cast (naturalRow η h.val h.property).natural_modulus_bound
  have hrad : (R.radical.absNorm:ℝ)≤(R.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hR))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=R))))
  have he : ((excluded (naturalRow η h.val h.property).character R).modulus.absNorm:ℝ)≤
      (A*rawFrequencyNorm h)*(R.absNorm:ℝ) := by
    rw [excluded_conductor _ _ hR,Nat.cast_mul]
    exact mul_le_mul hF hrad (Nat.cast_nonneg _) (by dsimp [A,rawFrequencyNorm];positivity)
  have hν : (((relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ)≤B := by
    change ((relativeCharacter M H hH η₀ θ).modulus.absNorm:ℝ)≤(M.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ)
    exact_mod_cast relativeCharacter_modulus M H hH η₀ θ
  have hp : (((excluded (naturalRow η h.val h.property).character R).product
      (relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ)≤
      ((excluded (naturalRow η h.val h.property).character R).modulus.absNorm:ℝ)*
        (((relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ) := by
    exact_mod_cast HeckePrimeScale.product_modulus_bound
      (excluded (naturalRow η h.val h.property).character R) (relativeCharacter M H hH η₀ θ).inverse.inverse
  have ht : ((twistedFamily M H hH
      ((excluded (naturalRow η h.val h.property).character R).product
        (relativeCharacter M H hH η₀ θ).inverse.inverse) θ').modulus.absNorm:ℝ)≤
      (((excluded (naturalRow η h.val h.property).character R).product
        (relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ)*(M.absNorm:ℝ) := by
    exact_mod_cast HeckePrimeScale.twisted_modulus_bound M H hH
      ((excluded (naturalRow η h.val h.property).character R).product
        (relativeCharacter M H hH η₀ θ).inverse.inverse) θ'
  have hb:=hp.trans (mul_le_mul he hν (Nat.cast_nonneg _) (by dsimp [A,rawFrequencyNorm];positivity))
  exact ht.trans (by convert mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg M.absNorm) using 1 <;> dsimp [K];ring)

theorem eventually_raw_relative_conductor (η η₀ : Character) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀q Bmask : ℝ,∀h : NonzeroFrequency,
      rawFrequencyNorm h≤Z^q →∀R : Ideal O,R≠0→(R.absNorm:ℝ)≤Z^Bmask→
      ∀θ θ',((twistedFamily M H hH
        ((excluded (naturalRow η h.val h.property).character R).product
          (relativeCharacter M H hH η₀ θ).inverse.inverse) θ').modulus.absNorm:ℝ)≤Z^(q+Bmask+δ) := by
  obtain ⟨K,hK,hbound⟩:=raw_relative_conductor_bound M H hH η η₀
  filter_upwards [(tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop K),
    eventually_gt_atTop (1:ℝ)] with Z hKZ hZ
  refine ⟨hZ,?_⟩
  intro q Bmask h hnorm R hR hmask θ θ'
  apply (hbound h R hR θ θ').trans
  calc
    _≤Z^δ*Z^q*Z^Bmask := mul_le_mul
      (mul_le_mul hKZ hnorm (by unfold rawFrequencyNorm;positivity) (Real.rpow_nonneg (by linarith) _))
      hmask (Nat.cast_nonneg _) (by positivity)
    _=Z^(q+Bmask+δ) := by
      rw [←Real.rpow_add (by linarith : 0<Z),←Real.rpow_add (by linarith : 0<Z)]
      congr 1
      ring

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.eventually_raw_relative_conductor
