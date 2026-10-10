import WeightedQRH.NumeratorFourierProfiles

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm CenteredMomentDetectorPlainCapacity
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open ProbeFinalAssemblyCertifiedBands CenteredMomentDetectorPlainMomentParameters
set_option maxHeartbeats 800000

lemma eventually_fixed_source_keep {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (η : Character) :
    ∀ᶠU:ℝ in atTop, ∀u:FreeRow, U^(1/100:ℝ) ≤ rowNorm u →
      weighted_initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val := by
  have ht : ∀ᶠU:ℝ in atTop, (weighted_sourceExceptionalBound F η:ℝ) < U^(1/100:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [ht] with U hU
  intro u hu
  apply (weighted_source_keep_iff F η u).mpr
  intro hh
  have hn : rowNorm u ≤ (weighted_sourceExceptionalBound F η:ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ) ≤ _
    exact_mod_cast weighted_source_exceptional_norm F η u hh
  exact (not_lt_of_ge (hu.trans hn)) hU

/-- Direct certified fixed-scale Fourier moments for the actual reflected
numerator and arbitrary selected physical prime slots. Both Fourier frequencies
are unrestricted; the degree and constant precede every scale and height. -/
theorem certified_reflected_fourier_moment {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃degree J:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ CenteredMomentEnergyWidthRanges.fineMesh 2 0 1 (3/4) (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ∀X₁ X₂:ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      length U X₁+length U X₂+6*(3/4)*(∑i,width i) ≤ 1 →
      ∀j k:Fin 2, ∀v w:ℝ,
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
        ≤ (C*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨bΦ,hbΦ,hsΦ⟩ := weighted_radialMajorant_support_bound
  obtain ⟨degree,control,henergy⟩ := weighted_terminal_energy F hbeta bΦ hbΦ
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨Cz,Cp,hCz,hCp,hbound⟩ := henergy η
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩ := numerator_fourier_profiles_control control
  let C := Cp*(1+diagonalControl radialMajorant)*Cprofile
  have hC : 0 < C := by
    have hd := diagonalControl_nonneg radialMajorant
    dsimp [C]; positivity
  have hmod : ∀ᶠU:ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ U^(D.t/4) :=
    (tendsto_rpow_atTop (div_pos D.t_pos (by norm_num))).eventually (eventually_ge_atTop _)
  refine ⟨degree,J,C,hC,?_⟩
  filter_upwards [hbound,hmod,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ)]
    with U henergy hmod hkeep hU
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hX₁max hX₂max hcap j k v w
  have hδ : 0 ≤ D.t/4 := div_nonneg D.t_pos.le (by norm_num)
  have hδtop : D.t/4 ≤ 1 := by linarith [D.t_small]
  have hc : length U X₁+length U X₂+6*(3/4)*(∑i,width i) ≤ 1+D.t/4 := by linarith
  have he := finite_physical_pair_positiveAt F rows η radialMajorant U bΦ (D.t/4)
    (CenteredMomentEnergyWidthRanges.fineMesh 2 0 1 (3/4) (D.t/4)) (D.t/4)
    hU.le hδ hδtop hsΦ radialMajorant_nonneg hmod (fun u hu=>(hrows u hu).2)
    (fun u hu=>hkeep u (hrows u hu).1) radialMajorant_one degree control Cp henergy.2
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w)
    X₁ X₂ hX₁ hX₂ hX₁max hX₂max hc
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏i,normalizedSlot η rowMaskElement 1 u.val (primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd := diagonalControl_nonneg radialMajorant
  have hp := hprofile j k v w
  have hx : U^(1+D.t/4+D.t/4) ≤ U^(1+D.t) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  calc
    _ ≤ (Cp*(1+diagonalControl radialMajorant))*
        (Cprofile*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*
        (1+height)^degree*U^(1+D.t) := by
      apply mul_le_mul _ hx (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCp.le) hp
        (sq_nonneg _) (by positivity)
    _ = _ := by dsimp [C]; ring

end SevenEighths.WeightedNumeratorReflection
end
end OAI
