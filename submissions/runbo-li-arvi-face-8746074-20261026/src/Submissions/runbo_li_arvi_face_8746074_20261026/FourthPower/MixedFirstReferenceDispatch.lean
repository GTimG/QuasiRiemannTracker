/- Copyright (c) 2026 Sil. Apache-2.0.
Actual selected-row reference dispatch after seed allocation and rebasing.
The selected cubic character is constructed, all original heights are
shifted exactly, and the old subunit reference is removed by its zero.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstPuncturedReference
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstCanonicalGeometry
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstSeededEnergy
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceCubicCharacter
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NonprincipalGate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstReferenceDispatch
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentSourceRectangle CenteredMomentCommonMaskEnergy CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily CenteredMomentUncenteredTerminal
open CenteredMomentLattice
open CenteredMomentTwist CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonProfile CenteredMomentOriginalRadialComparison MixedFixedSupport
open MixedPrincipalPair MixedPrincipalHeights MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonHeights MixedHeightEnergy MixedOriginalSource MixedLiveNormalization
open MixedFirstRebase MixedFirstSeededSource MixedFirstSeededEnergy MixedFirstPhysicalApplication
open MixedFirstPuncturedReference MixedFirstReferenceChoice MixedFirstCanonicalGeometry
open MixedFirstActualNonexceptional MixedCanonicalSource MixedCommonRestriction
open MixedCommonCoefficient MixedLiteralAllocation ReferencePrimeEnclosure
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The cubic product identity for the SAME original mask m. Unsupported
elements, including zero, are covered by their original natural zeros. -/
theorem cubic_selected_row (η : Character) (m f z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : ReferenceCubicCharacter.Data f) :
    rowTwist (elementHom (η.product r.character)) m 1 z n =
      rowTwist (elementHom η) m 1 (f^2*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hn0 : n ≠ 0 := by
      intro he
      apply hn.1
      simp only [he,Ideal.span_singleton_zero,Ideal.zero_eq_bot]
    have hr : elementCoeff r.character n = (idealRowHom f (Ideal.span {n}))^2 := by
      rw [← idealCoeff_span r.character hn0]
      exact r.on_supported _ hn
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,
      rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff (η.product r.character) n*coprimalityMask m n*
      idealRowHom (1^4*z) (Ideal.span {n}) = _
    rw [elementCoeff_product,hr]
    simp only [one_pow,one_mul,idealRowHom_argument_mul,
      idealRowHom_argument_pow f 2 (Ideal.span {n}) hn]
    rw [show elementHom η n = elementCoeff η n from rfl]
    ring
  · exact (rowTwist_zero_of_not_supported (elementHom (η.product r.character))
        m 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (elementHom η) m 1 (f^2*z) n hmLam hm2 hn).symm

/-- This is a constructed character presentation, not a hypothesis that
an arbitrary selected row is eligible for the short/reference estimate.
The full puncture R*seed is absent from its conductor. -/
structure SelectedCharacter (η : Character) (m : O) (F : Id) (z : O) where
  character : Character
  modulus_bound : character.modulus.absNorm ≤
    ReferenceCubicCharacter.conductorConstant*η.modulus.absNorm*(Ideal.span {m}).absNorm*
      (Ideal.span {(72 : O)}).absNorm*F.absNorm*(Ideal.span {z}).absNorm
  row_eq : ∀ n : O, elementCoeff character n =
    rowTwist (elementHom η) m 1 ((primaryGenerator F)^2*z) n
  on_supported : ∀ I : Id, Supported I → idealCoeff character I =
    idealCoeff η I*(idealRowHom (primaryGenerator F) I)^2*idealRowHom (m^6) I*idealRowHom z I
  off_supported : ∀ I : Id, ¬Supported I → idealCoeff character I = 0

theorem selected_character_exists (η : Character) (m : O) (F : Id) (z : O)
    (hm : m ≠ 0) (hF : Supported F) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    Nonempty (SelectedCharacter η m F z) := by
  have hf := supported_primaryGenerator_ne_zero F hF
  obtain ⟨r⟩ := ReferenceCubicCharacter.data_exists (primaryGenerator F) hf
  obtain ⟨χ,hχ,hrow⟩ := exists_row_character_with_conductor (η.product r.character) m 1 z
    hm one_ne_zero hz hmLam hm2
  have hid := idealCoeff_eq_row (η.product r.character) χ m 1 z hrow
  refine ⟨⟨χ,?_,?_,?_,?_⟩⟩
  · have hp := ReferenceCubicCharacter.product_modulus_bound η r.character
    have hb : (η.product r.character).modulus.absNorm ≤
        η.modulus.absNorm*(ReferenceCubicCharacter.conductorConstant*F.absNorm) := by
      have hh := hp.trans (Nat.mul_le_mul_left _ r.modulus_bound)
      simpa only [(primaryGenerator_spec F hf).1] using hh
    apply hχ.trans
    simp only [rowConductorBound,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow,one_mul]
    calc
      _ ≤ (η.modulus.absNorm*(ReferenceCubicCharacter.conductorConstant*F.absNorm))*
          (Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {z}).absNorm :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb))
      _ = _ := by ring
  · intro n
    exact (hrow n).trans (cubic_selected_row η m (primaryGenerator F) z n hmLam hm2 r)
  · intro I hI
    rw [hid I,idealCoeff_product,r.on_supported I hI]
    simp only [one_pow,mul_one,idealRowHom_argument_mul]
    ring
  · intro I hI
    rw [hid I,idealCoeff_product,r.off_supported I hI,mul_zero,zero_mul]

/-- Eligibility is the selected parameter Fgen²*z, not the untwisted z. -/
theorem selected_character_nonprincipal (η : Character) (m : O) (F : Id) (z : O)
    (r : SelectedCharacter η m F z) (Q : Id)
    (heligible : ¬FixedInducingRow η Q m ((primaryGenerator F)^2) z) :
    r.character.residue ≠ 1 :=
  CenteredMomentNonprincipalGate.actual_row_nonprincipal η r.character Q m
    ((primaryGenerator F)^2) z r.row_eq heligible

/-- Removing the already-present coefficient puncture also preserves the
actual nonprincipal row restriction. This is the companion of
selected_energy_mask; equality of energies alone would not justify it. -/
theorem selected_nonprincipal_mask_iff (η : Character) (Q R F : Id) (z : O)
    (hR : R ≠ 0) (hF : Supported F) (hz : z ≠ 0) :
    (¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) ((primaryGenerator F)^2) z) ↔
      ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z := by
  exact not_congr (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η Q
    fixedBadMask (idealGenerator R) ((primaryGenerator F)^2) z fixedBadMask_ne_zero
    (idealGenerator_ne_zero R hR) (pow_ne_zero _ (supported_primaryGenerator_ne_zero F hF))
    hz (dvd_mul_right _ _) (dvd_mul_left _ _))

/-- A total family used only on retained nonzero rows. The zero-row
fallback is immaterial to that family, and is never asserted eligible. -/
def selectedCharacterAt (η : Character) (m : O) (F : Id)
    (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (z : O) : Character :=
  if hz : z ≠ 0 then
    (Classical.choice (selected_character_exists η m F z hm hF hz hmLam hm2)).character
  else η

theorem selected_character_at_nonprincipal (η : Character) (m : O) (F : Id)
    (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (z : O) (hz : z ≠ 0) (Q : Id)
    (heligible : ¬FixedInducingRow η Q m ((primaryGenerator F)^2) z) :
    (selectedCharacterAt η m F hm hF hmLam hm2 z).residue ≠ 1 := by
  rw [selectedCharacterAt,dif_pos hz]
  exact selected_character_nonprincipal η m F z
    (Classical.choice (selected_character_exists η m F z hm hF hz hmLam hm2)) Q heligible

theorem selected_character_height (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) (I : Id) :
    selectedRowHom η m 1 z t F I = idealCoeff r.character I*(I.absNorm : ℂ)^(Complex.I*t) := by
  by_cases hI : Supported I
  · rw [r.on_supported I hI]
    change (idealRowHom (primaryGenerator F) I)^2*
      ((idealCoeff η I*idealRowHom (m^6*(1*z)) I)*(I.absNorm : ℂ)^(Complex.I*t)) = _
    simp only [one_mul,idealRowHom_argument_mul]
    ring
  · change selectedTwist F I*rowWeight η m 1 z t I = _
    rw [rowWeight_zero_of_not_supported η m 1 z t hmLam hm2 I hI,
      r.off_supported I hI,mul_zero,zero_mul]

private theorem residual_unit (Q : Finset Id) (h : (1 : Id) ≠ 0) :
    residualPool 1 h Q = Q := by
  ext I
  simp only [mem_residualPool,one_mul]

/-- No original column-height phase is discarded. It shifts ALL marked
coefficients and both ordinary norm-power frequencies by t. -/
theorem unit_source_height (s : Source ι a b) (ha : 0 < a) (hG : s.G = 1)
    (χ : Character) (t : ℝ) :
    normalization (s.X₁*s.X₂) s.P *
      (∑ I ∈ sourceColumns s,sourceCoefficient s ha 1 I*idealCoeff χ I*
        (I.absNorm : ℂ)^(Complex.I*t)) =
      residualPhase (s.X₁*s.X₂) s.d 1 t * weightedRow (shiftSource s t) ha 1 (idealCoeff χ) := by
  have he := original_height_row s ha χ 1 1 t
  simpa only [hG,residual_unit,isCoprime_one_left,one_dvd,and_self,ite_true,one_mul,
    weightedRow,sourceColumns,sourceCoefficient,MixedPrincipalAllocations.tuplePools,
    originalMaskedRow,originalColumn,shiftSource] using he

theorem selected_height_row (s : Source ι a b) (ha : 0 < a) (hG : s.G = 1)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    normalization (s.X₁*s.X₂) s.P * selectedPolynomial s ha 1 F η m 1 t z =
      residualPhase (s.X₁*s.X₂) s.d 1 t * weightedRow (shiftSource s t) ha 1 (idealCoeff r.character) := by
  rw [← unit_source_height s ha hG r.character t]
  apply congrArg (normalization (s.X₁*s.X₂) s.P * ·)
  unfold selectedPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  change (sourceCoefficient s ha 1 I*selectedTwist F I)*rowWeight η m 1 z t I = _
  rw [mul_assoc]
  change sourceCoefficient s ha 1 I*selectedRowHom η m 1 z t F I = _
  rw [selected_character_height η m F z hmLam hm2 r t I]
  ring

/-- A literal rectangle with the exact extracted height phase. Its
normalization is at the displayed rectangle lengths, not at a coarse cap. -/
def heightRectangle (s : Source ι a b) (ha : 0 < a) (χ : Character) (t X₁ X₂ : ℝ) : ℂ :=
  residualPhase (s.X₁*s.X₂) s.d 1 t *
    rectangleRow χ s.S s.H s.R s.pool (shiftSource s t).ν s.Wslot s.P
      (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) (s.t₁+t))
      (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) (s.t₂+t)) b X₁ X₂

/-- Actual centering, now for the selected physical row and its original
height. This is the identity used before any energy estimate. -/
theorem selected_centering (s : Source ι a b) (ha : 0 < a)
    (hd : s.d = (1,1)) (hG : s.G = 1) (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    heightRectangle s ha r.character t s.X₁ s.X₂ =
      normalization (s.X₁*s.X₂) s.P * selectedPolynomial s ha 1 F η m 1 t z +
        heightRectangle s ha r.character t s.Y₁ s.Y₂ := by
  have he := weighted_row_centering (shiftSource s t) ha hd r.character
  have hh := selected_height_row s ha hG η m F z hmLam hm2 r t
  have he' := congrArg (fun x : ℂ=>residualPhase (s.X₁*s.X₂) s.d 1 t*x) he
  rw [mul_add,←hh] at he'
  simpa only [heightRectangle,shiftSource] using he'

theorem height_rectangle_small (s : Source ι a b) (ha : 0 < a) (χ : Character)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hsmall : X₁ ≤ comparisonScale b ∨ X₂ ≤ comparisonScale b) :
    heightRectangle s ha χ t X₁ X₂ = 0 := by
  unfold heightRectangle rectangleRow tupleSum
  apply mul_eq_zero_of_right
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro v hv
  have hz := uncentered_small_factor s.R (shiftSource s t).ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) (s.t₁+t))
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) (s.t₂+t)) a b X₁ X₂ ha
    ((normPowerProfile_support _ _ _ _ _ _ _).trans s.hs₁)
    ((normPowerProfile_support _ _ _ _ _ _ _).trans s.hs₂)
    hX₁ hX₂ 1 1 1 one_ne_zero one_ne_zero hsmall v
  simp only [hz,mul_zero,zero_mul]

/-- A rebased old Y may be strictly below c. That still gives exactly the
uncentered row; no false equality Y1=c is inserted. -/
theorem selected_uncentered (s : Source ι a b) (ha : 0 < a)
    (hd : s.d = (1,1)) (hG : s.G = 1)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    normalization (s.X₁*s.X₂) s.P * selectedPolynomial s ha 1 F η m 1 t z =
      heightRectangle s ha r.character t s.X₁ s.X₂ := by
  have he := selected_centering s ha hd hG η m F z hmLam hm2 r t
  rw [height_rectangle_small s ha r.character t s.Y₁ s.Y₂
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) hY,add_zero] at he
  exact he.symm

private theorem normalization_nonzero (s : Source ι a b) :
    normalization (s.X₁*s.X₂) s.P ≠ 0 := by
  intro hz
  have he := normalization_sq (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i => zero_lt_one.trans_le (s.hP i))
  rw [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
  have hp : 0 < (s.X₁*s.X₂)*∏ i,s.P i :=
    mul_pos (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂))
      (Finset.prod_pos (fun i _ => zero_lt_one.trans_le (s.hP i)))
  exact (ne_of_gt (one_div_pos.mpr hp)) he.symm

theorem selected_small_factor_zero (s : Source ι a b) (ha : 0 < a)
    (hd : s.d = (1,1)) (hG : s.G = 1)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (hX : s.X₁ ≤ comparisonScale b ∨ s.X₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    selectedPolynomial s ha 1 F η m 1 t z = 0 := by
  have he := selected_uncentered s ha hd hG hY η m F z hmLam hm2 r t
  rw [height_rectangle_small s ha r.character t s.X₁ s.X₂
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) hX] at he
  exact (mul_eq_zero.mp he).resolve_left (normalization_nonzero s)

/-- The canonical slot-height identity also holds at zero, because the
canonical coefficient itself is zero there. -/
theorem canonical_height_all (ν : ι → Character) (R₀ : ι → Finset Id)
    (t₀ t : ℝ) :
    (fun i => heightCoefficient (slotCoefficient ν R₀ t₀ i) t) =
      slotCoefficient ν R₀ (t₀+t) := by
  funext i I
  by_cases hI : I = 0
  · subst I
    simp only [slotCoefficient,heightCoefficient,NativeFiniteHoles.holeCoefficient,
      map_zero,ite_self,zero_mul]
  · exact slot_coefficient_height ν R₀ t₀ t i I hI

/-- This is precisely the rectangle consumed by short_actual_reference.
Both ordinary heights and the marked height are shifted, with no change
to the original character or to the whole source puncture. -/
theorem height_rectangle_canonical (s : Source ι a b) (ha : 0 < a)
    (ν : ι → Character) (R₀ : ι → Finset Id) (t₀ : ℝ)
    (hν : s.ν = slotCoefficient ν R₀ t₀) (χ : Character) (t X₁ X₂ : ℝ) :
    heightRectangle s ha χ t X₁ X₂ =
      residualPhase (s.X₁*s.X₂) s.d 1 t *
        rectangleRow χ s.S s.H s.R s.pool (slotCoefficient ν R₀ (t₀+t)) s.Wslot s.P
          (phaseProfile s.W₁ ((s.t₁+t)/(2*Real.pi)))
          (phaseProfile s.W₂ ((s.t₂+t)/(2*Real.pi))) b X₁ X₂ := by
  have hv : (shiftSource s t).ν = slotCoefficient ν R₀ (t₀+t) := by
    change (fun i => heightCoefficient (s.ν i) t) = _
    rw [hν,canonical_height_all]
  unfold heightRectangle
  rw [hv,norm_power_profile_phase,norm_power_profile_phase]

theorem height_rectangle_norm (s : Source ι a b) (ha : 0 < a)
    (χ : Character) (t X₁ X₂ : ℝ) :
    ‖heightRectangle s ha χ t X₁ X₂‖ =
      ‖rectangleRow χ s.S s.H s.R s.pool (shiftSource s t).ν s.Wslot s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) (s.t₁+t))
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) (s.t₂+t)) b X₁ X₂‖ := by
  rw [heightRectangle,norm_mul,residual_phase_norm (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.d s.hd 1 one_ne_zero t,one_mul]

/-- Actual inherited reference scales shrink after allocation. -/
theorem seeded_reference_scales_le (s : Source ι a b) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (D : Id) (hD : D ≠ 0)
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D) :
    let r := seededRebasedSource s hb cover D hD B
    r.Y₁ ≤ s.Y₁ ∧ r.Y₂ ≤ s.Y₂ := by
  have hB := (allocation_data (MixedPrincipalAllocations.tuplePools s) D B.val
    (Finset.mem_filter.mp B.property).1).1
  change s.Y₁/(s.d.1*B.val (Sum.inr 0)).absNorm ≤ s.Y₁ ∧
    s.Y₂/(s.d.2*B.val (Sum.inr 1)).absNorm ≤ s.Y₂
  exact ⟨div_le_self (s.hL.trans_le s.hY₁).le
      (ideal_norm_one_le (mul_ne_zero s.hd.1 (hB _))),
    div_le_self (s.hL.trans_le s.hY₂).le
      (ideal_norm_one_le (mul_ne_zero s.hd.2 (hB _)))⟩

section Allocated
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M ≤ Hray)
variable (W : ℝ → ℂ) (Cap Lcap Z L : ℝ) (η₀ : Character)
variable (θ : ι → RayQuotient.Characters M Hray) (w σ freq : ι → ℝ) (t₀ : ℝ)
variable (R₀ : ι → Finset Id) (s : Source ι a b)
variable (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t₀ R₀ s)
variable (hb : 0 ≤ b) (cover : OriginalEnclosure s) (D : Id) (hD : D ≠ 0)
variable (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D) (q : ℝ)
variable (hZ : 1 ≤ Z) (hL : 0 ≤ L) (hLc : 2*L ≤ Lcap)
variable (hCap : b/comparisonScale b ≤ Cap) (hX₁ : s.X₁ ≤ Z^L) (hX₂ : s.X₂ ≤ Z^L)
variable (hq : comparisonScale b ≤ q)
variable (hq₁ : q ≤ (seededRebasedSource s hb cover D hD B).X₁)
variable (hq₂ : q ≤ (seededRebasedSource s hb cover D hD B).X₂)
local notation "live" => (seededRebasedSource s hb cover D hD B)
local notation "ref" => (allocatedReference M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t₀ R₀
  s hs hb cover D hD B q hZ hL hLc hCap hX₁ hX₂ hq hq₁ hq₂)

/-- This comparison is only at explicitly supplied rectangle lengths.
It does NOT assert equality of the differently centered source columns. -/
theorem allocated_rectangle_eq (ha : 0 < a) (χ : Character) (t X₁ X₂ : ℝ) :
    heightRectangle ref ha χ t X₁ X₂ = heightRectangle live ha χ t X₁ X₂ := by
  have hp : punctureProduct (enclosure (Cap*Z^Lcap)) (s.S.filter (fun Q => Q ∈ s.H)) =
      punctureProduct s.S s.H := by
    rw [← hs.1]
    unfold punctureProduct
    congr 1
    ext Q
    simp only [Finset.mem_filter]
    tauto
  unfold heightRectangle
  apply congrArg (residualPhase ((live).X₁*(live).X₂) (live).d 1 t * ·)
  change rectangleRow χ (enclosure (Cap*Z^Lcap)) (s.S.filter (fun Q => Q ∈ s.H))
    (live).R (live).pool (shiftSource live t).ν (live).Wslot (live).P _ _ b X₁ X₂ =
      rectangleRow χ s.S s.H (live).R (live).pool (shiftSource live t).ν (live).Wslot (live).P
        _ _ b X₁ X₂
  unfold rectangleRow tupleSum
  simp only [hp]
  rfl

/-- The concrete normalized original row equals the concrete centered
allocatedReference row plus its short rectangle. The original m, eta,
height, selected F and whole R*D are retained. q may be c or Z^l. -/
theorem allocated_selected_split (ha : 0 < a)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    normalization ((live).X₁*(live).X₂) (live).P * selectedPolynomial live ha 1 F η m 1 t z =
      normalization ((ref).X₁*(ref).X₂) (ref).P * selectedPolynomial ref ha 1 F η m 1 t z +
        heightRectangle ref ha r.character t q ((live).T/q) := by
  have hle := seeded_reference_scales_le s hb cover D hD B
  have hYlive : (live).Y₁ ≤ comparisonScale b ∨ (live).Y₂ ≤ comparisonScale b :=
    hY.elim (fun h => Or.inl (hle.1.trans h)) (fun h => Or.inr (hle.2.trans h))
  calc
    _ = heightRectangle live ha r.character t (live).X₁ (live).X₂ :=
      selected_uncentered live ha rfl rfl hYlive η m F z hmLam hm2 r t
    _ = heightRectangle ref ha r.character t (ref).X₁ (ref).X₂ :=
      (allocated_rectangle_eq M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t₀ R₀
        s hs hb cover D hD B q hZ hL hLc hCap hX₁ hX₂ hq hq₁ hq₂
        ha r.character t (live).X₁ (live).X₂).symm
    _ = _ := selected_centering ref ha rfl rfl η m F z hmLam hm2 r t

/-- The uncentered c-reference contributes exactly zero, so this branch
uses the constructed source without any reference-error estimate. -/
theorem allocated_uncentered_row (ha : 0 < a) (hcomparison : q = comparisonScale b)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    selectedPolynomial live ha 1 F η m 1 t z = selectedPolynomial ref ha 1 F η m 1 t z := by
  have he := allocated_selected_split M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t₀ R₀
    s hs hb cover D hD B q hZ hL hLc hCap hX₁ hX₂ hq hq₁ hq₂ ha hY η m F z hmLam hm2 r t
  have hz : heightRectangle ref ha r.character t q ((live).T/q) = 0 :=
    height_rectangle_small ref ha r.character t q ((live).T/q)
      ((ref).hL.trans_le (ref).hY₁) ((ref).hL.trans_le (ref).hY₂) (Or.inl hcomparison.le)
  rw [hz,add_zero] at he
  exact mul_left_cancel₀ (normalization_nonzero live) he

/-- Pointwise positive splitting on the original eligible row. Enlarging
only the centered energy to all rows is a subsequent positive step. -/
theorem allocated_selected_square (ha : 0 < a)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (r : SelectedCharacter η m F z) (t : ℝ) :
    ‖normalization ((live).X₁*(live).X₂) (live).P * selectedPolynomial live ha 1 F η m 1 t z‖^2 ≤
      2*(‖normalization ((ref).X₁*(ref).X₂) (ref).P * selectedPolynomial ref ha 1 F η m 1 t z‖^2 +
        ‖heightRectangle ref ha r.character t q ((live).T/q)‖^2) := by
  rw [allocated_selected_split M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t₀ R₀
    s hs hb cover D hD B q hZ hL hLc hCap hX₁ hX₂ hq hq₁ hq₂ ha hY η m F z hmLam hm2 r t]
  have hn := norm_add_le
    (normalization ((ref).X₁*(ref).X₂) (ref).P * selectedPolynomial ref ha 1 F η m 1 t z)
    (heightRectangle ref ha r.character t q ((live).T/q))
  have h₁ := norm_nonneg
    (normalization ((ref).X₁*(ref).X₂) (ref).P * selectedPolynomial ref ha 1 F η m 1 t z)
  have h₂ := norm_nonneg (heightRectangle ref ha r.character t q ((live).T/q))
  have h₀ := norm_nonneg
    (normalization ((ref).X₁*(ref).X₂) (ref).P * selectedPolynomial ref ha 1 F η m 1 t z +
      heightRectangle ref ha r.character t q ((live).T/q))
  nlinarith [sq_nonneg (‖normalization ((ref).X₁*(ref).X₂) (ref).P *
    selectedPolynomial ref ha 1 F η m 1 t z‖-‖heightRectangle ref ha r.character t q ((live).T/q)‖)]

/-- The actual positive energy dispatch retains the original keep mask
on BOTH sides. No reference bound is assumed. The centered keep may be
enlarged later by checked selected_energy_le_full, even when it depends F. -/
theorem allocated_selected_energy (ha : 0 < a)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (hm : m ≠ 0) (hF : Supported F)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) (t : ℝ)
    (keep : O → Prop) (hkeep : ∀ z,keep z → z ≠ 0)
    (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0 < K)
    (hΦsupport : Function.support (Φ : ℝ → ℂ) ⊆ Iic radial)
    (hΦ : ∀ z,0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    selectedEnergy live ha 1 F η m 1 t keep Φ K/sourceVolume live ≤
      2*(selectedEnergy ref ha 1 F η m 1 t keep Φ K/sourceVolume ref +
        radialEnergy (fun z => heightRectangle ref ha
          (selectedCharacterAt η m F hm hF hmLam hm2 z) t q ((live).T/q)) keep Φ K) := by
  let f : O → ℂ := fun z => normalization ((live).X₁*(live).X₂) (live).P *
    selectedPolynomial live ha 1 F η m 1 t z
  let g : O → ℂ := fun z => normalization ((ref).X₁*(ref).X₂) (ref).P *
    selectedPolynomial ref ha 1 F η m 1 t z
  let h : O → ℂ := fun z => heightRectangle ref ha
    (selectedCharacterAt η m F hm hF hmLam hm2 z) t q ((live).T/q)
  have hf := CenteredMomentEnergyCapacityRemoval.compact_radial_summable
    f keep Φ K radial hK hΦsupport
  have hg := CenteredMomentEnergyCapacityRemoval.compact_radial_summable
    g keep Φ K radial hK hΦsupport
  have hh := CenteredMomentEnergyCapacityRemoval.compact_radial_summable
    h keep Φ K radial hK hΦsupport
  have hpoint (z : O) (hz : keep z) : ‖f z‖^2 ≤ 2*(‖g z‖^2+‖h z‖^2) := by
    have hn := hkeep z hz
    let r := Classical.choice (selected_character_exists η m F z hm hF hn hmLam hm2)
    have hc : selectedCharacterAt η m F hm hF hmLam hm2 z = r.character := by
      rw [selectedCharacterAt,dif_pos hn]
    dsimp only [f,g,h]
    rw [hc]
    exact allocated_selected_square M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t₀ R₀
      s hs hb cover D hD B q hZ hL hLc hCap hX₁ hX₂ hq hq₁ hq₂ ha hY η m F z hmLam hm2 r t
  have he : radialEnergy f keep Φ K ≤ 2*(radialEnergy g keep Φ K+radialEnergy h keep Φ K) := by
    unfold radialEnergy
    calc
      _ ≤ ∑' z : O,2*((if keep z then ‖g z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)+
          (if keep z then ‖h z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)) := by
        apply hf.tsum_le_tsum _ ((hg.add hh).mul_left 2)
        intro z
        by_cases hz : keep z
        · simp only [hz,ite_true]
          convert mul_le_mul_of_nonneg_right (hpoint z hz) (hΦ z) using 1 <;> ring
        · simp only [hz,ite_false,zero_add,mul_zero,le_refl]
      _ = _ := by rw [tsum_mul_left,hg.tsum_add hh]
  have hnorm (r : Source (liveIndices B.val) a b) :
      radialEnergy (fun z => normalization (r.X₁*r.X₂) r.P *
        selectedPolynomial r ha 1 F η m 1 t z) keep Φ K =
      selectedEnergy r ha 1 F η m 1 t keep Φ K/sourceVolume r := by
    exact radial_normalization (r.X₁*r.X₂)
      (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)) r.P
      (fun i => zero_lt_one.trans_le (r.hP i)) _ keep Φ K
  dsimp only [f,g,h] at he
  rw [hnorm live,hnorm ref] at he
  exact he

end Allocated

end
end Candidate.FourthPower.MixedFirstReferenceDispatch
