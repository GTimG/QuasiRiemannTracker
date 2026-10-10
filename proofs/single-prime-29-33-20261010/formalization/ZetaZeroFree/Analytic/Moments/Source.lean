import ZetaZeroFree.Analytic.Moments.Exceptional

namespace ZetaZeroFree.Analytic.Moments

noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentOriginalRadialComparison
open CenteredMomentRadialPolynomialEnergy ConcreteTraceCRT
open CenteredMomentNaturalRowSource QuadraticInitialBound ProbeHighRowFamily ActualEisensteinCubic
local notation "O" => HeckeFamily.O

section SourceCharacter
open ProbeHighRowFamily CenteredMomentNaturalRowSource
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

lemma source_natural_coefficient (P : Finset (Ideal O)) (hP : ∀ I ∈ P, Prime I)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ P) (η : Character)
    (u : FreeRow) (label : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (sourceDetectorFamily P hP η u (rayCubeFamily M H hH u) label) I =
      if sourceMomentReverse M H label then
        conj (idealCoeff (naturalPlainCharacter (sourceMomentBase M H hH P hP η label) u.val) I)
      else idealCoeff (naturalPlainCharacter (sourceMomentBase M H hH P hP η label) u.val) I := by
  rw [source_family_moment_coeff M H hH P hP hbad η u label I, sourceMomentData_base]
  have he : idealCoeff ((momentData (sourceMomentBase M H hH P hP η label)).character
      (momentElement u)) I =
      idealCoeff (naturalPlainCharacter (sourceMomentBase M H hH P hP η label) u.val) I := by
    rw [momentData_coeff, rowMaskElement_eq_fixed]
    simpa only [naturalPlainCharacter, dite_eq_left u.property.1] using
      ((naturalRow (sourceMomentBase M H hH P hP η label) u.val u.property.1).ideal I).symm
  rw [he]

end SourceCharacter

/-- Finite unmarked rows are compared directly with the natural radial state.
The coefficient hypothesis records only the exact character presentation. -/
theorem finite_plain_bound
    (rows : Finset FreeRow) (χ : FreeRow → Character) (η : Character) (reverse : Bool)
    (Φ : 𝓢(ℝ, ℂ)) (radial U δ m L Mcap loss C : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ))
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hone : ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ x = 1)
    (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ)
    (hrow : ∀ u ∈ rows, rowNorm u ≤ U)
    (hnp : ∀ u ∈ rows, (naturalPlainCharacter η u.val).residue ≠ 1)
    (hc : ∀ u ∈ rows, ∀ I : Ideal O, idealCoeff (χ u) I =
      if reverse then conj (idealCoeff (naturalPlainCharacter η u.val) I)
      else idealCoeff (naturalPlainCharacter η u.val) I)
    (hw : 1 + δ ≤ Mcap) (hm : m ≤ L)
    (hend : AllNonprincipalAt (1 / 4) (9 / 4) radial 0 L Mcap loss U J S C)
    (j k : ℕ) (σ t : ℝ) :
    ∑ u ∈ rows, ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U ^ m) σ t *
      polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U ^ m) σ t‖ ^ 2 ≤
      C * diagonalControl Φ * ((detectorProfiles reverse j k σ t).control S) ^ 2 *
        U ^ (1 + δ + loss) := by
  let s := sourcePlainState η Φ radial U δ hU hδ hs hp hη
  let p := detectorProfiles reverse j k σ t
  let χn := fun z : O => excluded (naturalPlainCharacter η z) 1
  let f := fun z : O => polynomial (χn z) false (p.profile 0) (U ^ m) 0 0 *
    polynomial (χn z) false (p.profile 1) (U ^ m) 0 0
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 0 < U ^ m := Real.rpow_pos_of_pos hUp _
  have hnorm (u : FreeRow) (hu : u ∈ rows) (n : ℕ) :
      ‖polynomial (χ u) false ((logProfile^[n]) positiveAnnular) (U ^ m) σ t‖ =
      ‖polynomial (χn u.val) false (detectorSchwartz reverse n σ t) (U ^ m) 0 0‖ := by
    rw [norm_of_oriented_coefficients (χ u) (naturalPlainCharacter η u.val) reverse
      (hc u hu) false _ _ _ _ hX]
    have hW : (detectorSchwartz reverse n σ t : ℝ → ℂ) =
        twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ
          (orientedFrequency reverse t) := by funext x; exact detectorSchwartz_apply _ _ _ _ _
    rw [hW, polynomial_twistProfile]
    exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff _ _
      (fun I => (excluded_one_ideal _ I).symm) false _ _ _ _)
  have hroweq (u : FreeRow) (hu : u ∈ rows) :
      ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U ^ m) σ t *
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U ^ m) σ t‖ ^ 2 =
        ‖f u.val‖ ^ 2 := by
    rw [norm_mul, hnorm u hu j, hnorm u hu k]
    simp [f, p, detectorProfiles]
  have hsum : Summable (fun z : O => if sourcePlainKeep η z then
      ‖f z‖ ^ 2 * (Φ (‖eisEmbedding z‖ ^ 2 / U)).re else 0) := by
    have he := pair_radial_summable χn (fun _ => 1) (fun _ => 0) (fun _ => 0)
      (p.profile 0) (p.profile 1) (1/4) (9/4) (1/4) (9/4) (U ^ m) (U ^ m) 1
      (by norm_num) (by norm_num) hX hX (p.support 0) (p.support 1)
      (by intro z; simp) (sourcePlainKeep η) Φ U hUp
    simpa only [mul_one, f] using he
  have hfinite : (∑ u ∈ rows, ‖f u.val‖ ^ 2) ≤ s.energy (p.profile 0) (p.profile 1)
      (U ^ m) (U ^ m) 0 0 := by
    let rs := rows.image Subtype.val
    have heq : (∑ u ∈ rows, ‖f u.val‖ ^ 2) = ∑ z ∈ rs,
        if sourcePlainKeep η z then ‖f z‖ ^ 2 * (Φ (‖eisEmbedding z‖ ^ 2 / U)).re else 0 := by
      rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)]
      apply Finset.sum_congr rfl
      intro u hu
      have hk : sourcePlainKeep η u.val := ⟨u.property.1, hnp u hu⟩
      have hx : ‖eisEmbedding u.val‖ ^ 2 / U ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (sq_nonneg _) hUp.le, (div_le_one hUp).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hrow u hu
      simp only [ite_eq_left hk, hone _ hx, Complex.one_re, mul_one]
    rw [heq]
    exact sum_le_hasSum rs (fun z _ => by
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (hp _)
      · exact le_rfl) hsum.hasSum
  have hb := hend s hw (by simp [s, sourcePlainState]) (p.profile 0) (p.profile 1)
    (p.support 0) (p.support 1) (U ^ m) (U ^ m) 0 0 hX hX
    (Real.rpow_le_rpow_of_exponent_le hU hm) (Real.rpow_le_rpow_of_exponent_le hU hm)
  calc
    _ = ∑ u ∈ rows, ‖f u.val‖ ^ 2 := Finset.sum_congr rfl hroweq
    _ ≤ _ := hfinite.trans (by
      simpa only [s, p, sourcePlainState, NaturalPlainState.width,
        CenteredMomentFiniteProfileExceptional.Profiles.control,
        CenteredMomentFiniteProfileExceptional.sourceControl, norm_zero, add_zero, one_pow, mul_one] using hb)

end
end ZetaZeroFree.Analytic.Moments
