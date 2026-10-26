import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.WholeRegularSetup

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open Cycle61Moment Record12518109Natural HeckePrimeRay
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- A fixed linear conductor constant controls both actual clean zero
representatives and the literal relative ray family used by the slot. -/
theorem whole_core_conductor_bound (η η₀ : Character) :
    ∃K : ℝ,1≤K ∧∀u : FreeRow,
      (∀j,((naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character.modulus.absNorm:ℝ)≤K*rowNorm u) ∧
      (∀θ θ',((twistedFamily M H hH (relativeRayBase M H hH
        (excluded η (wholeAnchorMask M H hH η₀)) η₀ u.val u.property.1 θ) θ').modulus.absNorm:ℝ)≤K*rowNorm u) := by
  let ηc := excluded η (wholeAnchorMask M H hH η₀)
  obtain ⟨K₀,hK₀,hbound⟩ := (FixedUnmarkedDictionary.ofBases (cleanWholeBase M H hH η η₀)).natural_conductor_bound
  let A : ℝ := (ηc.modulus.absNorm:ℝ)*(CenteredMomentNaturalRowSource.fixedConductorFactor:ℝ)
  let B : ℝ := (M.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ)
  let K : ℝ := K₀+A*B*(M.absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have hExtra : 0≤A*B*(M.absNorm:ℝ) := mul_nonneg (mul_nonneg hA hB) (Nat.cast_nonneg _)
  refine ⟨K,by dsimp [K];linarith,?_⟩
  intro u
  have hu : 0≤rowNorm u := (rowNorm_ge_one u).trans' zero_le_one
  constructor
  · intro j
    exact (hbound u j).trans (mul_le_mul_of_nonneg_right (by dsimp [K];linarith) hu)
  · intro θ θ'
    have hF : ((naturalRow ηc u.val u.property.1).character.modulus.absNorm:ℝ)≤A*rowNorm u := by
      dsimp only [A,rowNorm]
      exact_mod_cast (naturalRow ηc u.val u.property.1).natural_modulus_bound
    have hν : (((relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ)≤B := by
      change ((relativeCharacter M H hH η₀ θ).modulus.absNorm:ℝ)≤(M.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ)
      exact_mod_cast relativeCharacter_modulus M H hH η₀ θ
    have hp : (((naturalRow ηc u.val u.property.1).character.product
        (relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ)≤
        ((naturalRow ηc u.val u.property.1).character.modulus.absNorm:ℝ)*
        (((relativeCharacter M H hH η₀ θ).inverse.inverse).modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound (naturalRow ηc u.val u.property.1).character
        (relativeCharacter M H hH η₀ θ).inverse.inverse
    have ht : ((twistedFamily M H hH (relativeRayBase M H hH ηc η₀ u.val u.property.1 θ) θ').modulus.absNorm:ℝ)≤
        ((relativeRayBase M H hH ηc η₀ u.val u.property.1 θ).modulus.absNorm:ℝ)*(M.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.twisted_modulus_bound M H hH
        (relativeRayBase M H hH ηc η₀ u.val u.property.1 θ) θ'
    have hprod := hp.trans (mul_le_mul hF hν (Nat.cast_nonneg _) (mul_nonneg hA hu))
    have he := ht.trans (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _))
    have hK : A*B*(M.absNorm:ℝ)≤K := by dsimp [K];linarith
    exact he.trans (by convert mul_le_mul_of_nonneg_right hK hu using 1 <;> ring)

theorem eventually_whole_core_conductor (η η₀ : Character) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀q : ℝ,∀u : FreeRow,rowNorm u≤Z^q →
      (∀j,(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character.modulus.absNorm≤Z^(q+δ)) ∧
      (∀θ θ',(twistedFamily M H hH (relativeRayBase M H hH
        (excluded η (wholeAnchorMask M H hH η₀)) η₀ u.val u.property.1 θ) θ').modulus.absNorm≤Z^(q+δ)) := by
  obtain ⟨K,hK,hbound⟩ := whole_core_conductor_bound M H hH η η₀
  filter_upwards [(tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop K),
    eventually_gt_atTop (1:ℝ)] with Z hKZ hZ
  refine ⟨hZ,?_⟩
  intro q u hu
  have hmul : K*rowNorm u≤Z^(q+δ) := by
    rw [Real.rpow_add (zero_lt_one.trans hZ)]
    exact (mul_le_mul hKZ hu ((rowNorm_ge_one u).trans' zero_le_one)
      (Real.rpow_nonneg (by linarith) _)).trans_eq (mul_comm _ _)
  exact ⟨fun j=>(hbound u).1 j |>.trans hmul,fun θ θ'=>(hbound u).2 θ θ' |>.trans hmul⟩

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
