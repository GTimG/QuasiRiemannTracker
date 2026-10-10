import ZetaZeroFree.Analytic.Moments.Plain
import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary

namespace ZetaZeroFree.Analytic.Moments

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentRadialEligibleEnergy
open CenteredMomentLattice QuadraticInitialBound
open CenteredMomentTwist
open CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentCommonMaskExpansion CenteredMomentPlainPositiveScale
local notation "O" => HeckeFamily.O

theorem deleted_plain_bound (a b η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)), Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (ψ : Character), ψ.residue ≠ 1 →
      ∀ (R : Ideal O) (X : ℝ), R ≠ 0 → 0 < X →
        ‖polynomial (excluded ψ R) false W X 0 0‖ ≤
          C * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            (ψ.modulus.absNorm : ℝ) * (R.radical.absNorm : ℝ) ^ η := by
  obtain ⟨S, C₀, hC₀, hplain⟩ := global_positive_scale a b ha
  obtain ⟨C₁, hC₁, hmass⟩ := euler_mass_subpower η hη
  refine ⟨S, C₀ * 9 * C₁, by positivity, ?_⟩
  intro W hs ψ hψ R X hR hX
  let T := CompletedGauss.primeSupport R
  have hT : ∀ P ∈ T, Prime P := CenteredMomentNaturalRowSource.support_prime R
  let D : ℝ := C₀ * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
    (ψ.modulus.absNorm : ℝ) * 9
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hp (U : Finset (Ideal O)) (hU : U ∈ T.powerset) :
      ‖polynomial ψ false W (X / (Ideal.absNorm (∏ P ∈ U, P) : ℝ)) 0 0‖ ≤ D := by
    have hn : 0 < (Ideal.absNorm (∏ P ∈ U, P) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun P hP =>
          (hT P (Finset.mem_powerset.mp hU hP)).ne_zero)))
    simpa [D, show (3 : ℝ) ^ 2 = 9 by norm_num] using hplain W hs ψ hψ _ 0 (div_pos hX hn)
  have he := normalized_finite_deletion_moebius ψ T hT W (schwartz_decayTwo W) X hX
  change polynomial (excluded ψ R) false W X 0 0 = _ at he
  rw [he]
  calc
    _ ≤ ∑ U ∈ T.powerset, ‖plainCoefficient ψ U *
        polynomial ψ false W (X / (Ideal.absNorm (∏ P ∈ U, P) : ℝ)) 0 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ U ∈ T.powerset, weight (∏ P ∈ U, P) * D := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      exact mul_le_mul
        (plainCoefficient_norm ψ U (fun P hP => hT P (Finset.mem_powerset.mp hU hP)))
        (hp U hU) (norm_nonneg _) (weight_nonneg _)
    _ = (∏ P ∈ T, (1 + weight P)) * D := by rw [← Finset.sum_mul, deletion_mass]
    _ ≤ (C₁ * (R.radical.absNorm : ℝ) ^ η) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      have hh := (deletion_le_euler T hT).trans (hmass T hT)
      simpa only [T, CenteredMomentAllocatedNaturalSource.primeSupport_product_radical R hR] using hh
    _ = _ := by dsimp [D]; ring

/-- Induction by a fixed nonprincipal character costs only deletion of its old zeros. -/
theorem induced_mask_polynomial (χ ψ : Character)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) (R : Ideal O) (hR : R ≠ 0)
    (W : ℝ → ℂ) (X σ t : ℝ) :
    polynomial (excluded χ R) false W X σ t =
      polynomial (excluded ψ (χ.modulus * R)) false W X σ t := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold summand HeckeDyadic.coefficient
  rw [CenteredMomentNaturalRowSource.excluded_ideal χ R hR,
    CenteredMomentNaturalRowSource.excluded_ideal ψ (χ.modulus * R)
      (mul_ne_zero χ.modulus_ne_bot hR), hind I.val, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

/-- A plain mixed endpoint for all rows induced by bounded nonprincipal conductors.
The primitive characters and redundant masks may vary with the row. -/
theorem fixed_induced_mixed (a b ε B Q : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hB : 0 ≤ B) (hQ : 0 < Q) :
    ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ ψ : O → Character) (r : Radial) (R : Ideal O) (Z m X₁ X₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → r.scale = Z ^ m → 0 < X₁ → 0 < X₂ →
        (∀ z, r.keep z → CenteredExceptionalProfile.InducedBy (χ z) (ψ z)) →
        (∀ z, r.keep z → (ψ z).residue ≠ 1) →
        (∀ z, r.keep z → ((ψ z).modulus.absNorm : ℝ) ≤ Q) →
        (∀ z, r.keep z → (((χ z).modulus * R).radical.absNorm : ℝ) ≤ Z ^ B) →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
          C * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 * Z ^ (m + ε) := by
  let η : ℝ := ε / (4 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηB : 4 * (B * η) ≤ ε := by
    have he : η * (4 * (B + 1)) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨S, C₀, hC₀, hplain⟩ := deleted_plain_bound a b η ha hη
  refine ⟨S, C₀ ^ 4 * Q ^ 4, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ ψ r R Z m X₁ X₂ hR hZ hm hscale hX₁ hX₂ hind hψ hmod hmask
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0 ≤ B₁ := apply_nonneg _ _
  have hB₂ : 0 ≤ B₂ := apply_nonneg _ _
  let D : ℝ := C₀ ^ 2 * (B₁ * B₂) * Q ^ 2 * (Z ^ (B * η)) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hd := diagonalControl_nonneg r.profile
  have hp (z : O) (hk : r.keep z) (W : 𝓢(ℝ, ℂ))
      (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (X : ℝ) (hX : 0 < X) :
      ‖polynomial (excluded (χ z) R) false W X 0 0‖ ≤
        C₀ * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * Q * Z ^ (B * η) := by
    rw [induced_mask_polynomial (χ z) (ψ z) (hind z hk) R hR]
    have hh := hplain W hs (ψ z) (hψ z hk) ((χ z).modulus * R) X
      (mul_ne_zero (χ z).modulus_ne_bot hR) hX
    apply hh.trans
    gcongr
    · exact hmod z hk
    · apply (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmask z hk) hη.le).trans_eq
      rw [← Real.rpow_mul hz.le]
  have hpoint (z : O) (hk : r.keep z) :
      ‖polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
        polynomial (excluded (χ z) R) false W₂ X₂ 0 0‖ ≤ D := by
    rw [norm_mul]
    exact (mul_le_mul (hp z hk W₁ hs₁ X₁ hX₁) (hp z hk W₂ hs₂ X₂ hX₂)
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp [D, B₁, B₂]; ring)
  have hh := CenteredMomentPlainGlobalEnergy.radial_bound_on_keep _ r D hD hpoint
  change radialEnergy _ r.keep r.profile r.scale ≤ _ at hh
  rw [hscale, max_eq_right (Real.one_le_rpow hZ hm)] at hh
  have hpow : Z ^ m * ((Z ^ (B * η)) ^ 2) ^ 2 ≤ Z ^ (m + ε) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  rw [hscale]
  apply hh.trans
  calc
    _ = (C₀ ^ 4 * Q ^ 4 * diagonalControl r.profile * (B₁ * B₂) ^ 2) *
        (Z ^ m * ((Z ^ (B * η)) ^ 2) ^ 2) := by dsimp [D]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem fixed_induced_mixed_height (a b ε B Q : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hB : 0 ≤ B) (hQ : 0 < Q) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ ψ : O → Character) (r : Radial) (R : Ideal O) (Z m X₁ X₂ t₁ t₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → r.scale = Z ^ m → 0 < X₁ → 0 < X₂ →
        (∀ z, r.keep z → CenteredExceptionalProfile.InducedBy (χ z) (ψ z)) →
        (∀ z, r.keep z → (ψ z).residue ≠ 1) →
        (∀ z, r.keep z → ((ψ z).modulus.absNorm : ℝ) ≤ Q) →
        (∀ z, r.keep z → (((χ z).modulus * R).radical.absNorm : ℝ) ≤ Z ^ B) →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 t₁ *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 t₂) r.keep r.profile r.scale ≤
          C * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + ε) := by
  obtain ⟨S₀, C₀, hC₀, he⟩ := fixed_induced_mixed a b ε B Q ha hε hB hQ
  obtain ⟨J, S, C₁, hC₁, hheight⟩ := mixed_height_profile_control a b ha S₀
  refine ⟨J, S, C₀ * C₁, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ ψ r R Z m X₁ X₂ t₁ t₂ hR hZ hm hscale hX₁ hX₂ hind hψ hmod hmask
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  have hh := he V₁ V₂ hsV₁ hsV₂ χ ψ r R Z m X₁ X₂ hR hZ hm hscale hX₁ hX₂ hind hψ hmod hmask
  rw [mixed_height_energy_eq a b ha χ r R W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂] at hh
  have hd := diagonalControl_nonneg r.profile
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hheight W₁ W₂ hs₁ hs₂ t₁ t₂)
      (mul_nonneg hC₀.le hd)) (Real.rpow_nonneg (zero_le_one.trans hZ) _)).trans_eq
  ring

section CertifiedZeroExtraction
open Filter CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional

lemma natural_energy_eq (Z B radial a b : ℝ) (ha : 0 < a)
    (s : NaturalState Z B radial) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    s.plainEnergy p 0 X₁ X₂ = radialEnergy
      (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false (p.profile 0) X₁ 0 0 *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false (p.profile 1) X₂ 0 0)
      s.radial.keep s.radial.profile s.radial.scale := by
  rw [s.plainEnergy_eq_zero]
  unfold CenteredMomentCoreFloor.zeroEnergy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · have hz := s.row_ne_zero z hk
    simp only [ite_eq_left hk]
    rw [CenteredMomentPlainGlobalEnergy.zero_row_norm s.character
      (excluded (naturalPlainCharacter s.character z) s.puncture) s.mask 1 z
      (by simpa [naturalPlainCharacter, hz, NaturalState.mask] using
        (naturalRow s.character z hz).masked_element s.puncture s.puncture_ne_zero)
      (p.profile 0) (p.profile 1) a b ha (p.support 0) (p.support 1)
      ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤) 0 X₁ X₂ hX₁ hX₂,
      norm_mul]
  · simp [hk]

def NonfixedMixedAt (Q : Ideal O) (a b radial B L Mcap ε Z : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z B radial, s.fixedModulus = Q → s.width ≤ Mcap →
    ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
    ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      radialEnergy (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false W₁ X₁ 0 t₁ *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false W₂ X₂ 0 t₂) s.radial.keep s.radial.profile s.radial.scale ≤
        C * diagonalControl s.radial.profile *
          ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

theorem zero_at_independent_heights (a b : ℝ) (ha : 0 < a) (S₀ : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ Cheight : ℝ, 0 < Cheight ∧
      ∀ (Q : Ideal O) (radial B L Mcap ε Z C : ℝ) (J₀ : ℕ),
        0 ≤ Z → 0 ≤ C → ZeroAt Q a b radial B L Mcap ε Z J₀ S₀ C →
        NonfixedMixedAt Q a b radial B L Mcap ε Z J S (C * Cheight) := by
  obtain ⟨J, S, Cheight, hCheight, he⟩ := mixed_height_profile_control a b ha S₀
  refine ⟨J, S, Cheight, hCheight, ?_⟩
  intro Q radial B L Mcap ε Z C J₀ hZ hC hz s hQ hw W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  let p : Profiles a b := {
    profile := ![V₁, V₂]
    support := by
      intro i
      fin_cases i
      · exact hsV₁
      · exact hsV₂ }
  have hh := hz s hQ hw p 0 X₁ X₂ hX₁ hX₂ hLX₁ hLX₂
  rw [natural_energy_eq Z B radial a b ha s p X₁ X₂ hX₁ hX₂] at hh
  change radialEnergy (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false V₁ X₁ 0 0 * polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false V₂ X₂ 0 0) s.radial.keep s.radial.profile s.radial.scale ≤ _ at hh
  rw [mixed_height_energy_eq a b ha (naturalPlainCharacter s.character) s.radial
    s.puncture W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂] at hh
  simp only [norm_zero, add_zero, one_pow, mul_one] at hh
  have hp : p.control S₀ = (S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁) *
      (S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂) := rfl
  rw [hp] at hh
  have hd := diagonalControl_nonneg s.radial.profile
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (he W₁ W₂ hs₁ hs₂ t₁ t₂) (mul_nonneg hC hd))
    (Real.rpow_nonneg hZ _)).trans_eq
  ring

end CertifiedZeroExtraction

lemma fixed_inducing_natural_character (η : Character) (Q R : Ideal O)
    (hR : R ≠ 0) (z : O) (hz : z ≠ 0)
    (hfixed : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator R) 1 z) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ Q ≤ ψ.modulus ∧
      CenteredExceptionalProfile.InducedBy (excluded (naturalPlainCharacter η z) R) ψ := by
  obtain ⟨χ, ψ, hprim, hind, hQ, hrow⟩ := hfixed
  refine ⟨ψ, hprim, hQ, HeckeMaskDescent.inducedBy_mask χ
    (excluded (naturalPlainCharacter η z) R) ψ 1 ?_ hind⟩
  intro n
  simp only [isCoprime_one_right, ite_true]
  rw [hrow]
  simpa [naturalPlainCharacter, hz] using (naturalRow η z hz).masked_element R hR n

lemma fixed_inducing_natural_nonprincipal (η : Character) (Q R : Ideal O)
    (hR : R ≠ 0) (z : O) (hz : z ≠ 0)
    (hn : (naturalPlainCharacter η z).residue ≠ 1)
    (hfixed : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator R) 1 z) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue ≠ 1 ∧
      Q ≤ ψ.modulus ∧
      CenteredExceptionalProfile.InducedBy (excluded (naturalPlainCharacter η z) R) ψ := by
  obtain ⟨ψ, hp, hQ, hind⟩ := fixed_inducing_natural_character η Q R hR z hz hfixed
  have hmask := excludePrimes_mask (naturalPlainCharacter η z)
    (CompletedGauss.primeSupport R) (support_prime R)
  have hχ : (excluded (naturalPlainCharacter η z) R).residue ≠ 1 := by
    intro h
    exact hn ((HeckeFiniteDeletion.principal_iff_of_mask _ _ hmask).mp h)
  refine ⟨ψ, hp, ?_, hQ, hind⟩
  intro h
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask _ _ hind).mpr h)

lemma polynomial_excluded_top (χ : Character) (W : ℝ → ℂ) (X σ t : ℝ) :
    polynomial (excluded χ ⊤) false W X σ t = polynomial χ false W X σ t := by
  have hc (I : Ideal O) : IsCoprime I ⊤ := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_right
  unfold polynomial summand HeckeDyadic.coefficient
  simp only [excluded_ideal χ ⊤ top_ne_bot, hc, ite_true]

lemma mixed_radial_partition (χ : O → Character) (r : Radial) (P : O → Prop)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (a b X₁ X₂ t₁ t₂ : ℝ) (hb : 0 ≤ b)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    radialEnergy (fun z => polynomial (χ z) false W₁ X₁ 0 t₁ *
        polynomial (χ z) false W₂ X₂ 0 t₂) r.keep r.profile r.scale =
      radialEnergy (fun z => polynomial (χ z) false W₁ X₁ 0 t₁ *
        polynomial (χ z) false W₂ X₂ 0 t₂) (fun z => r.keep z ∧ P z) r.profile r.scale +
      radialEnergy (fun z => polynomial (χ z) false W₁ X₁ 0 t₁ *
        polynomial (χ z) false W₂ X₂ 0 t₂) (fun z => r.keep z ∧ ¬ P z) r.profile r.scale := by
  have hs (keep : O → Prop) := CenteredMomentRadialPolynomialEnergy.pair_radial_summable
    χ (fun _ => (1 : ℂ)) (fun _ => t₁) (fun _ => t₂) W₁ W₂ a b a b X₁ X₂ 1
    hb hb hX₁ hX₂ hs₁ hs₂ (by simp) keep r.profile r.scale r.scale_pos
  simp only [mul_one] at hs
  unfold radialEnergy
  rw [← Summable.tsum_add (hs (fun z => r.keep z ∧ P z)) (hs (fun z => r.keep z ∧ ¬ P z))]
  apply tsum_congr
  intro z
  by_cases hk : r.keep z <;> by_cases hp : P z <;> simp [hk, hp]

theorem all_natural_mixed_join (a b radial B Bfixed L Mcap ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hBfixed : 0 ≤ Bfixed) (hε : 0 < ε)
    (Q : Ideal O) (hQ : Q ≠ 0) (Jn : ℕ) (Sn : Finset (ℕ × ℕ)) (Cn : ℝ) :
    ∃ Jf : ℕ, ∃ Sf : Finset (ℕ × ℕ), ∃ Cf : ℝ, 0 < Cf ∧
      ∀ Z : ℝ, NonfixedMixedAt Q a b radial B L Mcap ε Z Jn Sn Cn →
      ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
      (s.puncture.absNorm : ℝ) ≤ Z ^ B →
      (∀ z, s.radial.keep z →
        ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤ Z ^ Bfixed) →
      ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
        Cn * diagonalControl s.radial.profile *
          ((Sn.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (Sn.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ Jn * (1 + ‖t₂‖) ^ Jn * Z ^ (s.width + ε) +
        Cf * diagonalControl s.radial.profile *
          ((Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ Jf * (1 + ‖t₂‖) ^ Jf * Z ^ (s.rowWidth + ε) := by
  have hQnorm : 0 < (Q.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  obtain ⟨Jf, Sf, Cf, hCf, hf⟩ := fixed_induced_mixed_height a b ε Bfixed Q.absNorm
    ha hε hBfixed hQnorm
  refine ⟨Jf, Sf, Cf, hCf, ?_⟩
  intro Z hn s hw hpuncture hmasked W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  let P : O → Prop := fun z => ¬ CenteredExceptionalProfile.FixedInducingRow s.character Q
    (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z
  let rn : Radial := { s.radial with keep := fun z => s.radial.keep z ∧ P z }
  let rf : Radial := { s.radial with keep := fun z => s.radial.keep z ∧ ¬ P z }
  let sn : CenteredMomentEnergyState.NaturalState Z B radial := {
    character := s.character, fixedModulus := Q, puncture := s.puncture, radial := rn,
    rowWidth := s.rowWidth, characterWidth := s.characterWidth,
    base_ge_one := s.base_ge_one, row_nonneg := s.row_nonneg, character_nonneg := s.character_nonneg,
    scale_eq := s.scale_eq, modulus_bound := by simpa only [one_mul] using s.modulus_bound,
    puncture_ne_zero := s.puncture_ne_zero, puncture_bound := hpuncture,
    radial_support := s.radial_support, row_ne_zero := fun z hk => s.row_ne_zero z hk.1,
    nonexceptional := fun _ hk => hk.2 }
  have hn' := hn sn rfl hw W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hex (z : O) (hk : rf.keep z) := fixed_inducing_natural_nonprincipal s.character Q
    s.puncture s.puncture_ne_zero z (s.row_ne_zero z hk.1) (s.row_nonprincipal z hk.1)
    (Classical.not_not.mp hk.2)
  choose ψ hp hψ hψQ hi using fun z => fun hk : rf.keep z => hex z hk
  let χ : O → Character := fun z => excluded (naturalPlainCharacter s.character z) s.puncture
  let ψf : O → Character := fun z => if hk : rf.keep z then ψ z hk else χ z
  have hi' (z : O) (hk : rf.keep z) : CenteredExceptionalProfile.InducedBy (χ z) (ψf z) := by
    simpa [ψf, hk] using hi z hk
  have hψ' (z : O) (hk : rf.keep z) : (ψf z).residue ≠ 1 := by
    have hψeq : ψf z = ψ z hk := by
      exact dite_eq_left hk
    rw [hψeq]
    exact hψ z hk
  have hmod (z : O) (hk : rf.keep z) : ((ψf z).modulus.absNorm : ℝ) ≤ Q.absNorm := by
    simp only [ψf, dite_eq_left hk]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (hψQ z hk)))
  have hf' := hf W₁ W₂ hs₁ hs₂ χ ψf rf ⊤ Z s.rowWidth X₁ X₂ t₁ t₂ top_ne_bot
    s.base_ge_one s.row_nonneg s.scale_eq hX₁ hX₂ hi' hψ' hmod
    (by intro z hk; simpa [χ] using hmasked z hk.1)
  simp only [polynomial_excluded_top] at hf'
  rw [NaturalPlainState.energy, mixed_radial_partition χ s.radial P W₁ W₂ a b X₁ X₂ t₁ t₂
    hb hs₁ hs₂ hX₁ hX₂]
  exact add_le_add hn' hf'

lemma mixed_uniform_control_mono (S T : Finset (ℕ × ℕ)) (hST : S ⊆ T)
    (J K : ℕ) (hJK : J ≤ K) (W₁ W₂ : 𝓢(ℝ, ℂ)) (t₁ t₂ : ℝ) :
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J ≤
    ((T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
      (1 + ‖t₁‖) ^ K * (1 + ‖t₂‖) ^ K := by
  have hp : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂) ≤
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂) :=
    mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) W₁)
      (Seminorm.le_def.mp (Finset.sup_mono hST) W₂) (apply_nonneg _ _) (apply_nonneg _ _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp 2
  have ht₁ := pow_le_pow_right₀ (by linarith [norm_nonneg t₁] : 1 ≤ 1 + ‖t₁‖) hJK
  have ht₂ := pow_le_pow_right₀ (by linarith [norm_nonneg t₂] : 1 ≤ 1 + ‖t₂‖) hJK
  exact mul_le_mul (mul_le_mul hpow ht₁ (by positivity) (by positivity)) ht₂
    (by positivity) (by positivity)

theorem all_natural_mixed_uniform_join (a b radial B Bfixed L Mcap ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hBfixed : 0 ≤ Bfixed) (hε : 0 < ε)
    (Q : Ideal O) (hQ : Q ≠ 0) (Jn : ℕ) (Sn : Finset (ℕ × ℕ)) (Cn : ℝ) (hCn : 0 ≤ Cn) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, NonfixedMixedAt Q a b radial B L Mcap ε Z Jn Sn Cn →
      ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
      (s.puncture.absNorm : ℝ) ≤ Z ^ B →
      (∀ z, s.radial.keep z →
        ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤ Z ^ Bfixed) →
      ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
        C * diagonalControl s.radial.profile *
          ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε) := by
  obtain ⟨Jf, Sf, Cf, hCf, he⟩ := all_natural_mixed_join a b radial B Bfixed L Mcap ε
    ha hb hBfixed hε Q hQ Jn Sn Cn
  refine ⟨max Jn Jf, Sn ∪ Sf, Cn + Cf, by linarith, ?_⟩
  intro Z hn s hw hpuncture hmasked W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hh := he Z hn s hw hpuncture hmasked W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hN := mixed_uniform_control_mono Sn (Sn ∪ Sf) Finset.subset_union_left
    Jn (max Jn Jf) (le_max_left _ _) W₁ W₂ t₁ t₂
  have hF := mixed_uniform_control_mono Sf (Sn ∪ Sf) Finset.subset_union_right
    Jf (max Jn Jf) (le_max_right _ _) W₁ W₂ t₁ t₂
  have hd := diagonalControl_nonneg s.radial.profile
  have hz : 0 ≤ Z := zero_le_one.trans s.base_ge_one
  have hZwidth : Z ^ (s.rowWidth + ε) ≤ Z ^ (s.width + ε) :=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by
      dsimp [NaturalPlainState.width]; linarith [s.character_nonneg])
  have hN' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (mul_nonneg hCn hd)) (Real.rpow_nonneg hz (s.width + ε))
  have hF' := mul_le_mul
    (mul_le_mul_of_nonneg_left hF (mul_nonneg hCf.le hd)) hZwidth
    (Real.rpow_nonneg hz _) (by positivity)
  apply hh.trans
  convert add_le_add hN' hF' using 1 <;> ring

def AllNaturalMixedAt (a b radial B Bfixed L Mcap ε Z : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
    (s.puncture.absNorm : ℝ) ≤ Z ^ B →
    (∀ z, s.radial.keep z →
      ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤ Z ^ Bfixed) →
    ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
    ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
      C * diagonalControl s.radial.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
        (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

def AllNonprincipalAt (a b radial B L Mcap ε Z : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
    (s.puncture.absNorm : ℝ) ≤ Z ^ B →
    ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
    ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
      C * diagonalControl s.radial.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
        (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

lemma live_masked_modulus_budget (Z B radial Mcap : ℝ)
    (s : NaturalPlainState Z B radial 1) (hw : s.width ≤ Mcap) (hradial : 0 ≤ radial)
    (hcap : (fixedConductorFactor : ℝ) * radial ≤ Z) (z : O)
    (hk : s.restrictLive.radial.keep z) :
    ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤
      Z ^ (Mcap + B + 1) := by
  have hz := s.row_ne_zero z hk.1
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  have hzn : ((Ideal.span {z}).absNorm : ℝ) ≤ radial * Z ^ s.rowWidth := by
    rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hk.2)
  have hη : (s.character.modulus.absNorm : ℝ) ≤ Z ^ s.characterWidth := by
    simpa only [one_mul] using s.modulus_bound
  have hnatural : ((naturalPlainCharacter s.character z).modulus.absNorm : ℝ) ≤
      (fixedConductorFactor : ℝ) * radial * Z ^ s.width := by
    simpa [naturalPlainCharacter, hz, NaturalPlainState.width, add_comm s.rowWidth s.characterWidth]
      using (naturalRow s.character z hz).modulus_power_bound Z s.characterWidth
        s.rowWidth radial hZ hradial hη hzn
  let χ := excluded (naturalPlainCharacter s.character z) s.puncture
  have hrad : (χ.modulus.radical.absNorm : ℝ) ≤ χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I := χ.modulus))))
  have hnorm : (χ.modulus.absNorm : ℝ) =
      ((naturalPlainCharacter s.character z).modulus.absNorm : ℝ) *
        (s.puncture.radical.absNorm : ℝ) := by
    change (((naturalPlainCharacter s.character z).modulus *
      ∏ P ∈ CompletedGauss.primeSupport s.puncture, P).absNorm : ℝ) = _
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    simp only [map_mul, Nat.cast_mul]
  apply hrad.trans
  rw [hnorm]
  have hpow := Real.rpow_le_rpow_of_exponent_le s.base_ge_one hw
  have hmod := mul_le_mul hnatural s.puncture_bound (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hradial) (Real.rpow_nonneg hZ.le _))
  apply hmod.trans
  calc
    _ ≤ (Z * Z ^ Mcap) * Z ^ B := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      exact mul_le_mul hcap hpow (Real.rpow_nonneg hZ.le _) hZ.le
    _ = (Z ^ (1 : ℝ) * Z ^ Mcap) * Z ^ B := by rw [Real.rpow_one]
    _ = Z ^ (1 + Mcap + B) := by rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    _ = _ := by congr 1; ring


def sourcePlainKeep (η : Character) (z : O) : Prop :=
  z ≠ 0 ∧ (naturalPlainCharacter η z).residue ≠ 1

def sourcePlainState (η : Character) (Φ : 𝓢(ℝ, ℂ)) (radial U δ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ) :
    NaturalPlainState U 0 radial 1 where
  character := η
  puncture := 1
  radial := {
    keep := sourcePlainKeep η
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth := 1
  characterWidth := δ
  displayedSupport := ⊤
  displayed_squarefree := by rw [← Ideal.one_eq_top]; exact squarefree_one
  displayed_bound := by simpa using Real.one_le_rpow hU hδ
  displayed_zeros := le_top
  base_ge_one := hU
  row_nonneg := by norm_num
  character_nonneg := hδ
  scale_eq := by simp
  modulus_bound := by simpa only [one_mul] using hη
  puncture_ne_zero := one_ne_zero
  puncture_bound := by simp [Ideal.radical_top]
  radial_support := hs
  row_ne_zero := fun _ hk => hk.1
  row_nonprincipal := fun _ hk => hk.2

lemma plain_state_zero_energy_eq (Z B radial Cfixed a b : ℝ) (ha : 0 < a)
    (s : NaturalPlainState Z B radial Cfixed) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentCoreFloor.zeroEnergy s.character
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator s.puncture)
      1 0 W₁ W₂ X₁ X₂ s.radial = s.energy W₁ W₂ X₁ X₂ 0 0 := by
  unfold CenteredMomentCoreFloor.zeroEnergy NaturalPlainState.energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · have hz := s.row_ne_zero z hk
    simp only [ite_eq_left hk]
    rw [CenteredMomentPlainGlobalEnergy.zero_row_norm s.character
      (excluded (naturalPlainCharacter s.character z) s.puncture) _ 1 z
      (by simpa [naturalPlainCharacter, hz] using
        (naturalRow s.character z hz).masked_element s.puncture s.puncture_ne_zero)
      W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤) 0 X₁ X₂ hX₁ hX₂, norm_mul]
  · simp [hk]

section DetectorNaturalSource
open HeckeDetectorRawFiber CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainStateDictionary
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
variable {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem source_retained_plain_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (Φ : 𝓢(ℝ, ℂ)) (radial δ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ)
    (j k : ℕ) (σ t : ℝ) :
    retainedSourceEnergy (sourcePlainKeep η) F η ∅ j k σ t Φ =
      (sourcePlainState η Φ radial U δ hU hδ hs hp hη).energy
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (U ^ F.m) (U ^ F.m) 0 0 := by
  let s := sourcePlainState η Φ radial U δ hU hδ hs hp hη
  let p := detectorProfiles F.reverse j k σ t
  rw [← plain_state_zero_energy_eq U 0 radial 1 (1 / 4) (9 / 4) (by norm_num)
    s (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) (U ^ F.m) (U ^ F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)]
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  simp [s, sourcePlainState, p, detectorProfiles, CenteredMomentCoreFloor.zeroEnergy,
    CenteredMomentCoreFloor.zeroRow, CenteredMomentInductionEnergy.energy,
    CenteredMomentRetainedEnergy.positiveSlotRow]

theorem source_retained_plain_bound (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (Φ : 𝓢(ℝ, ℂ)) (radial δ L Mcap loss C : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ))
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ)
    (hw : 1 + δ ≤ Mcap) (hL : F.m ≤ L)
    (hend : AllNonprincipalAt (1 / 4) (9 / 4) radial 0 L Mcap loss U J S C)
    (j k : ℕ) (σ t : ℝ) :
    retainedSourceEnergy (sourcePlainKeep η) F η ∅ j k σ t Φ ≤
      C * diagonalControl Φ * ((detectorProfiles F.reverse j k σ t).control S) ^ 2 *
        U ^ (1 + δ + loss) := by
  let s := sourcePlainState η Φ radial U δ hU hδ hs hp hη
  let p := detectorProfiles F.reverse j k σ t
  have hX : 0 < U ^ F.m := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _
  have hXL : U ^ F.m ≤ U ^ L := Real.rpow_le_rpow_of_exponent_le hU hL
  have he := hend s hw (by simp [s, sourcePlainState]) (p.profile 0) (p.profile 1)
    (p.support 0) (p.support 1) (U ^ F.m) (U ^ F.m) 0 0 hX hX hXL hXL
  rw [source_retained_plain_eq F η Φ radial δ hU hδ hs hp hη j k σ t]
  simpa only [s, p, sourcePlainState, NaturalPlainState.width,
    CenteredMomentFiniteProfileExceptional.Profiles.control,
    CenteredMomentFiniteProfileExceptional.sourceControl, norm_zero, add_zero, one_pow, mul_one] using he

end DetectorNaturalSource

/-- D.26, with the first-transform variables measured before rounding. -/
theorem first_exceptional_saving (c D q B g σ : ℝ)
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hg : g ≤ max (D - c) 0 + σ)
    (hcost : max (3 * c - 5 * D) 0 ≤ q + 6 * B) :
    2 * c / 3 - 5 * σ / 6 ≤ c / 6 + 5 * D / 6 + q / 6 + B - 5 * g / 6 := by
  by_cases hD : c ≤ D
  · rw [max_eq_left (by linarith : 0 ≤ D - c)] at hg
    linarith
  · rw [max_eq_right (by linarith : D - c ≤ 0)] at hg
    have hm := le_max_left (3 * c - 5 * D) 0
    linarith

/-- D.28: cancellation is preserved through the final divisor allocation. -/
theorem divisor_cancellation_saving (t r₁ r₂ r : ℝ)
    (_ht₁ : t ≤ r₁) (ht₂ : t ≤ r₂) :
    t - r₁ - r₂ - max (r - r₁) 0 ≤ -r := by
  by_cases h : r₁ ≤ r
  · rw [max_eq_left (by linarith : 0 ≤ r - r₁)]
    linarith
  · rw [max_eq_right (by linarith : r - r₁ ≤ 0)]
    linarith

/-- The exact optimization in D.29. -/
theorem centered_exceptional_deficit (A M v : ℝ) :
    A - 5 * M / 6 - 2 * v / 3 - max (M / 4 - v) 0 ≤ A - M := by
  by_cases h : v ≤ M / 4
  · rw [max_eq_left (by linarith : 0 ≤ M / 4 - v)]
    linarith
  · rw [max_eq_right (by linarith : M / 4 - v ≤ 0)]
    linarith

end
end ZetaZeroFree.Analytic.Moments
