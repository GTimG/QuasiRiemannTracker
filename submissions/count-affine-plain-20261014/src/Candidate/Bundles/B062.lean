/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B019
import Candidate.Bundles.B020
import Candidate.Bundles.B061
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

/- BEGIN ORIGINAL Cycle25.Energy.Physical.FourierProfiles; sha256 117bd8dab512a95ebb655926238eabdecd99bddfc903cdaff6b7e911389047a8 -/
section
                                                  
                                                                

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyProfiles
open CenteredMomentEnergyReferenceChild CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentDetectorDictionary
open CenteredMomentNaturalMaskedFloor CenteredMomentRetainedProfile CenteredMomentLattice

/-- Fixed conjugated annular derivative tests used after reflecting the numerator. -/
def numeratorAnnular (j : Fin 2) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (derivativeChoice annulusTemplate.profile j)

lemma numeratorAnnular_apply (j : Fin 2) :
    (numeratorAnnular j : ℝ → ℂ) =
      fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x) := by
  change (fun x=>conj (derivativeChoice annulusTemplate.profile j x)) = _
  rw [derivativeChoice_apply]
  rfl

lemma numeratorAnnular_support (j : Fin 2) :
    Function.support (numeratorAnnular j : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4) := by
  rw [numeratorAnnular_apply,conjugate_profile_support]
  intro x hx
  have hh := scaleTest_support (fun y:ℝ=>(annulus y:ℂ)) (1/4) 1 annulus_support j hx
  exact ⟨hh.1,hh.2.trans (by norm_num)⟩

def numeratorFourierProfiles (j k : Fin 2) (v w : ℝ) : Profiles (1/4) (9/4) :=
  independentProfiles (by norm_num) (numeratorAnnular j) (numeratorAnnular k)
    (numeratorAnnular_support j) (numeratorAnnular_support k) (-2*Real.pi*v) (-2*Real.pi*w)

/-- The two unbounded Fourier frequencies have independently controlled polynomial
growth. This fixed degree is chosen before any final contour-height parameter. -/
theorem numerator_fourier_profiles_control (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ, ∃C : ℝ, 0 < C ∧ ∀j k : Fin 2, ∀v w : ℝ,
      (numeratorFourierProfiles j k v w).control S ^2 ≤
        C*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨J,T,C,hC,hc⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) S
  let A : ℝ := 1+∑j:Fin 2, sourceControl T (numeratorAnnular j)
  have hA : 0 < A := by
    have hh := Finset.sum_nonneg (fun j (_:j∈Finset.univ)=>sourceControl_nonneg T (numeratorAnnular j))
    dsimp [A]; linarith
  have hA' (j : Fin 2) : sourceControl T (numeratorAnnular j) ≤ A := by
    have hh := Finset.single_le_sum
      (fun j (_:j∈Finset.univ)=>sourceControl_nonneg T (numeratorAnnular j)) (Finset.mem_univ j)
    dsimp [A]; linarith
  let B := C*A*(1+2*Real.pi)^J
  have hB : 0 < B := by dsimp [B]; positivity
  have hone (j : Fin 2) (v : ℝ) :
      sourceControl S (normPowerProfile (numeratorAnnular j) (1/4) (9/4) (by norm_num)
        (numeratorAnnular_support j) ((numeratorAnnular j).smooth ⊤) (-2*Real.pi*v))
        ≤ B*(1+‖v‖)^J := by
    have hh := hc (numeratorAnnular j) (numeratorAnnular_support j) (-2*Real.pi*v)
    have hv : 1+‖-2*Real.pi*v‖ ≤ (1+2*Real.pi)*(1+‖v‖) := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
      norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
      nlinarith [Real.pi_pos,norm_nonneg v]
    calc
      _ ≤ C*sourceControl T (numeratorAnnular j)*(1+‖-2*Real.pi*v‖)^J := hh
      _ ≤ C*A*((1+2*Real.pi)*(1+‖v‖))^J := by
        gcongr
        exact hA' j
      _ = _ := by dsimp [B]; rw [mul_pow]; ring
  refine ⟨J,B^4,by positivity,?_⟩
  intro j k v w
  have hh : (numeratorFourierProfiles j k v w).control S ≤
      (B*(1+‖v‖)^J)*(B*(1+‖w‖)^J) := by
    simpa only [numeratorFourierProfiles,independentProfiles,Profiles.control,
      Fin.zero_eta,ite_true,show (1:Fin 2)≠0 by decide,ite_false] using
      mul_le_mul (hone j v) (hone k w) (sourceControl_nonneg _ _) (by positivity)
  calc
    _ ≤ ((B*(1+‖v‖)^J)*(B*(1+‖w‖)^J))^2 :=
      pow_le_pow_left₀ (Profiles.control_nonneg _ _) hh 2
    _ = _ := by ring

lemma numerator_fourier_polynomial_zero (χ : Character) (j k : Fin 2)
    (v w X : ℝ) :
    polynomial χ false ((numeratorFourierProfiles j k v w).profile 0) X 0 0 =
      polynomial χ false (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x))
        X 0 (-2*Real.pi*v) := by
  change polynomial χ false (normPowerProfile _ _ _ _ _ _ _) X 0 0 = _
  rw [twist_polynomial,numeratorAnnular_apply]

lemma numerator_fourier_polynomial_one (χ : Character) (j k : Fin 2)
    (v w X : ℝ) :
    polynomial χ false ((numeratorFourierProfiles j k v w).profile 1) X 0 0 =
      polynomial χ false (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k x))
        X 0 (-2*Real.pi*w) := by
  change polynomial χ false (normPowerProfile _ _ _ _ _ _ _) X 0 0 = _
  rw [twist_polynomial,numeratorAnnular_apply]

lemma inverse_annular_norm_eq {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (u : FreeRow) (j : Fin 2)
    (v X : ℝ) (hX : 0 < X) :
    ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X 0 (2*Real.pi*v)‖ =
    ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x))
        X 0 (-2*Real.pi*v)‖ := by
  have hh := polynomial_inverse_norm (rowCharacter F.S F.exclusions.prime u) false
    (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x)) X 0 (-2*Real.pi*v) hX
  simp only [Complex.conj_conj,neg_mul,neg_neg] at hh
  rw [hh,numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad]
  congr 2 <;> ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.FourierProfiles -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.Terminal; sha256 4fba83f4e94359da0df68feeba47bbe1eb0dabef0967ff3fc6f419547731c2db -/
section
                                          
                              
                                                  

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace OAI.SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem weighted_terminal_positive_energy {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop, 1 < U ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (Cycle25.Energy.commonMesh 2 0 1 (D.t/4))
        (33/50) (33/50) 2 (D.t/4) κ U η₀ (weighted_sourceFixedIdeal F) degree control C := by
  have hsupport : Function.support (fun x=>conj (F.W x)) ⊆ Set.Icc (1:ℝ) 2 := by
    intro x hx
    exact F.complex_support (by simpa using hx)
  obtain ⟨degree,control,hbound⟩ := Cycle25.Energy.terminal_positive_at (α:=Fin D.N)
    F.modulus ⊤ le_top (fun x=>conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1
    (33/50) (33/50) 2 κ (D.t/4) (by norm_num) hsupport
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) hκlo hκhi
    (div_pos D.t_pos (by norm_num)) hbeta hκbeta
  refine ⟨degree,control,?_⟩
  intro η₀
  exact hbound η₀ (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2

theorem weighted_terminal_zero_energy {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop, 1 < U ∧
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 2 2
        (D.t/4) U degree control C := by
  obtain ⟨degree,control,hbound⟩ := ZetaZeroFree.Analytic.Moments.Unconditional.nonfixed_zero_at
    F.modulus (1/4) (9/4) bΦ 0 2 2 (D.t/4) (by norm_num) (by norm_num)
    (by norm_num) hbΦ (by norm_num) (by norm_num) (div_pos D.t_pos (by norm_num))
  refine ⟨degree,control,?_⟩
  intro η₀
  exact hbound η₀ (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2

end OAI.SevenEighths.Cycle25WeightedNumeratorPhysical

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The positive contour assumptions are explicit; the empty-slot endpoint is unconditional. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.Terminal -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.CertifiedFourier; sha256 bfcf0da80cfcd5f49fae665f71b0d88f284a251f74e327dd62ab811419c413cc -/
section
                                              
                                       

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
open CenteredMomentRowNorm
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
set_option maxHeartbeats 800000

lemma eventually_fixed_source_keep {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) :
    ∀ᶠU:ℝ in atTop, ∀u:FreeRow, U^(1/100:ℝ) ≤ rowNorm u →
      initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val := by
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
theorem certified_reflected_fourier_moment {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) :
    ∃degree J:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ∀X₁ X₂:ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1 →
      ∀j k:Fin 2, ∀v w:ℝ,
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
        ≤ (C*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨bΦ,hbΦ,hsΦ⟩ := radialMajorant_support_bound
  obtain ⟨degree,control,henergy⟩ := weighted_terminal_positive_energy F κ hκlo hκhi hbeta hκbeta bΦ hbΦ
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨Cp,hCp,hbound⟩ := henergy η
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
  have hc : length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1+D.t/4 := by linarith
  have he := finite_physical_pair_positiveAt F rows η radialMajorant U bΦ (D.t/4)
    (Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) (D.t/4) κ
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

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.CertifiedFourier -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.CertifiedZero; sha256 d8998bf78f03ccb77767f78fa68fc1dac0ea59b0a4d8feb5ea96ce5006a23b8b -/
section
                                               

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

end
/- END ORIGINAL Cycle25.Energy.Physical.CertifiedZero -/
