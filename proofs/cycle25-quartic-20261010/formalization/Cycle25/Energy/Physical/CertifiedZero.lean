import Cycle25.Energy.Physical.CertifiedFourier

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
set_option maxHeartbeats 800000

/-- The empty-slot terminal estimate has no capacity condition on the two
plain lengths. Here each is permitted up to U². -/
theorem finite_pair_zeroAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ ε : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hzero : ZeroAt (internalQ (weighted_sourceFixedIdeal F) η) (1/4) (9/4) bΦ 0 2 2
      ε U degree control C)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U^(2:ℝ)) (hX₂max : X₂ ≤ U^(2:ℝ)) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*U^(1+δ+ε) := by
  let state := initialState η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ bΦ U δ hU hδ hs hp hη
  have hwidth : state.width ≤ 2 := by change 1+δ ≤ 2; linarith
  have hz := hzero state rfl hwidth p 0 X₁ X₂ hX₁ hX₂ hX₁max hX₂max
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ U bΦ δ hU hδ hs hp hη hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) (by intro i; exact zero_lt_one)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at he
  exact he.trans (by simpa [state,initialState,NaturalState.width,NaturalState.mask,
    NaturalState.plainEnergy] using hz)

/-- Actual inverse physical row Fourier moment for the empty selected family,
including reflected annuli with lengths larger than the square-root scale. -/
theorem certified_reflected_zero_fourier_moment {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    ∃J:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀X₁ X₂:ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ U^(2:ℝ) → X₂ ≤ U^(2:ℝ) →
      ∀j k:Fin 2, ∀v w:ℝ,
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w)‖^2)
        ≤ (C*U^(1+D.t))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨bΦ,hbΦ,hsΦ⟩ := radialMajorant_support_bound
  obtain ⟨degree,control,henergy⟩ := weighted_terminal_zero_energy F bΦ hbΦ
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨Cz,hCz,hbound⟩ := henergy η
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩ := numerator_fourier_profiles_control control
  let C := Cz*(1+diagonalControl radialMajorant)*Cprofile
  have hC : 0 < C := by
    have hd := diagonalControl_nonneg radialMajorant
    dsimp [C]; positivity
  have hmod : ∀ᶠU:ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ U^(D.t/4) :=
    (tendsto_rpow_atTop (div_pos D.t_pos (by norm_num))).eventually (eventually_ge_atTop _)
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hbound,hmod,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ)]
    with U henergy hmod hkeep hU
  refine ⟨hU,?_⟩
  intro rows hrows X₁ X₂ hX₁ hX₂ hX₁max hX₂max j k v w
  have hδ : 0 ≤ D.t/4 := div_nonneg D.t_pos.le (by norm_num)
  have hδtop : D.t/4 ≤ 1 := by linarith [D.t_small]
  have he := finite_pair_zeroAt F rows η radialMajorant U bΦ (D.t/4) (D.t/4)
    hU.le hδ hδtop hsΦ radialMajorant_nonneg hmod (fun u hu=>(hrows u hu).2)
    (fun u hu=>hkeep u (hrows u hu).1) radialMajorant_one degree control Cz henergy.2
    (numeratorFourierProfiles j k v w) X₁ X₂ hX₁ hX₂ hX₁max hX₂max
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂]
  rw [heq]
  apply he.trans
  have hd := diagonalControl_nonneg radialMajorant
  have hp := hprofile j k v w
  have hx : U^(1+D.t/4+D.t/4) ≤ U^(1+D.t) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  calc
    _ ≤ (Cz*(1+diagonalControl radialMajorant))*
        (Cprofile*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*U^(1+D.t) := by
      apply mul_le_mul _ hx (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCz.le) hp
        (sq_nonneg _) (by positivity)
    _ = _ := by dsimp [C]; ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
