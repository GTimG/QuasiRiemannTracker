/-
R1: `SelectedRootEnergyCap K` (quantifier plumbing over `cap_body`), hence `SelectedRootEnergy K` for
`K ∈ [0.500001, 3/4]` via `Peel` and `Swap`.
-/
import Submissions.arvi_selected_leaf.R1.Body

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open Cycle61Moment
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyState CenteredMomentEnergyCapacityRemoval
open CenteredMomentNaturalRowSource
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRayMaskedFloor
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open ConcretePrimeRowBridge
open Qrh.JointDetector
local notation "O" => HeckeFamily.O

/-- The `scaleTest` bound of a short profile through the scale operator. -/
theorem scale_bound (S S₁ : Finset (ℕ×ℕ)) (C₁ Csc : ℝ) (hC₁ : 0 < C₁) (hCsc : C₁ ≤ Csc)
    (hS₁S : S₁ ⊆ S)
    (hscale : ∀ V : 𝓢(ℝ,ℂ), ({((0:ℕ),(0:ℕ))} : Finset (ℕ×ℕ)).sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (DetectorDictionaryInverseUniform.scaleCLM V) ≤ C₁ * S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) V)
    (V : 𝓢(ℝ,ℂ)) (x : ℝ) :
    ‖CenteredMomentScaleSupremum.scaleTest (V : ℝ → ℂ) 1 x‖ ≤ Csc * sourceControl S V := by
  have h1 : CenteredMomentScaleSupremum.scaleTest (V : ℝ → ℂ) 1 x =
      DetectorDictionaryInverseUniform.scaleCLM V x := by
    simp [CenteredMomentScaleSupremum.scaleTest, DetectorDictionaryInverseUniform.scaleCLM_apply]
  rw [h1]
  have h2 := norm_le_control {((0:ℕ),(0:ℕ))} (by simp) (DetectorDictionaryInverseUniform.scaleCLM V) x
  have h4 := control_mono S S₁ hS₁S V
  calc ‖DetectorDictionaryInverseUniform.scaleCLM V x‖
      ≤ sourceControl {((0:ℕ),(0:ℕ))} (DetectorDictionaryInverseUniform.scaleCLM V) := h2
    _ ≤ C₁ * S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) V := hscale V
    _ ≤ C₁ * sourceControl S V := mul_le_mul_of_nonneg_left h4 hC₁.le
    _ ≤ Csc * sourceControl S V := mul_le_mul_of_nonneg_right hCsc (sourceControl_nonneg _ _)

/-- **R1 in the capped ordered case.** -/
theorem cap_proof (K : ℝ) (hK1 : (500001/1000000:ℝ) ≤ K) (hK2 : K ≤ 3/4) :
    SelectedRootEnergyCap K := by
  intro ε hε smin Mmin Mcap hsmin hMmin hMcap
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = min ε 1 / 20 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact div_pos (lt_min hε one_pos) (by norm_num)
  have hu1 : u ≤ 1/20 := by rw [hu]; have := min_le_right ε 1; linarith only [this]
  have huε : u ≤ ε/20 := by rw [hu]; have := min_le_left ε 1; linarith only [this]
  obtain ⟨Preq, hPreq⟩ : ∃ x : ℝ, x = 4*(Mcap+1) + 30 := ⟨_, rfl⟩
  have hPreq0 : 0 ≤ Preq := by rw [hPreq]; linarith only [hMmin, hMcap]
  obtain ⟨meshMax₀, hmesh₀, hnorm⟩ := FineCanonicalFromNorm.actual_norm
    NaturalSelectedNorm.natural_selected_cell_norm Mmin Mcap smin u Preq hMmin hMcap hsmin hu0 hPreq0
  refine ⟨meshMax₀, hmesh₀, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Knorm, hKnorm, hnormEv⟩ :=
    hnorm mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ (by linarith only [hbΦ])
  obtain ⟨auxCap, hauxCap⟩ : ∃ x : ℝ,
      x = FineDetectorWords.detectorAuxiliarySourceCap Preq (Mcap+1) := ⟨_, rfl⟩
  have hauxCap1 : 4*(Mcap+1) + 31 ≤ auxCap := by
    rw [hauxCap, FineDetectorWords.detectorAuxiliarySourceCap, hPreq]
    linarith only [le_max_left (4*(Mcap+1) + 30) (3*(Mcap+1))]
  have hauxCap0 : 0 < auxCap := by linarith only [hauxCap1, hMmin, hMcap]
  obtain ⟨εd, hεdD⟩ : ∃ x : ℝ, x = u / (auxCap * (2 + (Fintype.card α : ℝ))) := ⟨_, rfl⟩
  have hεd : 0 < εd := by rw [hεdD]; positivity
  have hεdmul : εd * (auxCap * (2 + (Fintype.card α : ℝ))) = u := by
    rw [hεdD]; field_simp
  obtain ⟨cη, hcη⟩ : ∃ x : ℝ, x = ∑ j, ((anchors j).modulus.absNorm : ℝ) + 1 := ⟨_, rfl⟩
  have hcη1 : 1 ≤ cη := by
    rw [hcη]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      (Nat.cast_nonneg ((anchors j).modulus.absNorm) : (0:ℝ) ≤ _))
    linarith only [this]
  obtain ⟨Cscale, hCscale⟩ : ∃ x : ℝ, x = cη * ((Ideal.span {fixedBadMask}).absNorm : ℝ) *
      ((Ideal.span {(72:O)}).absNorm : ℝ) * bΦ := ⟨_, rfl⟩
  have hNm0 : (0:ℝ) < ((Ideal.span {fixedBadMask}).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have hN720 : (0:ℝ) < ((Ideal.span {(72:O)}).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O) ≠ 0)))
  have hbΦ0 : (0:ℝ) < bΦ := by linarith only [hbΦ]
  have hCs : 0 < Cscale := by
    rw [hCscale]
    have : (0:ℝ) < cη := by linarith only [hcη1]
    positivity
  have hMcap0 : 0 < Mcap := lt_of_lt_of_le hMmin hMcap
  obtain ⟨n, Se, Ce, De, La, hCe, hDe, hLa, _, hreflEv⟩ :=
    R1.reflected_class (u/(Mcap+1)) Cscale u Mcap (by positivity) hCs hu0
  obtain ⟨S₁, C₁, hC₁, hscale⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    DetectorDictionaryInverseUniform.scaleCLM {((0:ℕ),(0:ℕ))}
  obtain ⟨S, hS⟩ : ∃ x : Finset (ℕ×ℕ), x = Se ∪ S₁ ∪ {((0:ℕ),(0:ℕ))} := ⟨_, rfl⟩
  have hS0 : ((0:ℕ),(0:ℕ)) ∈ S := by rw [hS]; simp
  have hSeS : Se ⊆ S := by rw [hS]; intro x hx; simp [hx]
  have hS₁S : S₁ ⊆ S := by rw [hS]; intro x hx; simp [hx]
  obtain ⟨LW, hLW⟩ : ∃ LW, ∀ x, ‖W x‖ ≤ LW :=
    hW.continuous.bounded_above_of_compact_support (HasCompactSupport.intro isCompact_Icc
      (fun x hx => by
        by_contra h'
        exact hx (hWs h')))
  have hLW0 : 0 ≤ LW := (norm_nonneg _).trans (hLW 0)
  obtain ⟨Csc, hCsc⟩ : ∃ x : ℝ, x = max 1 C₁ := ⟨_, rfl⟩
  have hCsc1 : 1 ≤ Csc := by rw [hCsc]; exact le_max_left _ _
  have hCscC : C₁ ≤ Csc := by rw [hCsc]; exact le_max_right _ _
  obtain ⟨C₆, hC₆, hsum⟩ := R1.root_class_sum
  refine ⟨2*n, S,
    ((9/4) * (2 * Knorm * (max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd))^(2 + Fintype.card α) *
        ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
          (128 * La^2 * (128*(9/4))) * Csc^2) * (max 1 (256 * LW^2))^(Fintype.card α)) *
      (R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + (9/4) * 2^(Fintype.card α)) + C₆ * bΦ +
        R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * ((9/4) * 2^(Fintype.card α)))), ?_, ?_⟩
  · have := le_max_left (1:ℝ) (Qrh.JointDetector.idealDivisorConstant εd hεd)
    have := R1.rootZeta_nonneg (1 + u/(Mcap+1))
    positivity
  filter_upwards [hnormEv, hreflEv, eventually_ge_atTop ((9/4:ℝ)^2 * 2^(Fintype.card α))]
    with Z hZ93 hZref hZbig
  refine ⟨hZ93.1, ?_⟩
  intro j st hchar hpunc hMlow hMup T D θ w σ v t height hw hwm hσ₁ hσ₂ hh hv hsD hsT p X₁ X₂ hX₁ hX₂
    h21 hl₁ hl₂
  have hηmod : ((st.character.modulus.absNorm : ℕ) : ℝ) ≤ cη := by
    rw [hchar, hcη]
    have := Finset.single_le_sum (f := fun j' => ((anchors j').modulus.absNorm : ℝ))
      (fun j' _ => Nat.cast_nonneg _) (Finset.mem_univ j)
    linarith only [this]
  have hsD' : smin ≤ ∑ k : D, w k := by rw [Finset.sum_coe_sort D w]; exact hsD
  exact cap_body K ε Mmin Mcap u auxCap εd Knorm cη Cscale Ce De La Csc C₆ LW bΦ Z t height n Se S
    (by linarith only [hK1]) (by linarith only [hK2]) hMmin hu0 hu1 huε hauxCap1 rayM H hbΦ hεd
    hεdmul hKnorm hCscale hCs hCe hDe hLa hLW0 hS0 hSeS hCsc1
    (scale_bound S S₁ C₁ Csc hC₁ hCscC hS₁S hscale) hC₆ hsum hZ93.1 hZbig hZref.2 st hpunc hηmod hMlow
    hMup T w hw hsT
    (fun (i : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i I => R1.annular_coeff_le _ W LW (Z^(w i)) (σ i) (v i) I
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ93.1) _) (by linarith only [hσ₁ i]) hWs hLW)
    (fun z => Z^(K * ∑ i ∈ D, w i) ≤ blockMass rayM H hH W η₀ st.character θ w σ v t Z D z)
    (fun r cores Y hY1 hY2 hc => hauxCap ▸ hZ93.2 j st hchar hpunc hMlow hMup D (fun k => θ k) (fun k => w k)
      (fun k => σ k) (fun k => v k) t height (fun k => hw k) (fun k => hwm k) (fun k => hσ₁ k)
      (fun k => hσ₂ k) hh (fun k => hv k) hsD' K Y r cores ⟨hK1, hK2⟩ hY1 hY2 (fun u hu => by
        obtain ⟨h1, hz, h2, h3⟩ := hc u hu
        refine ⟨h1, hz, h2, ?_⟩
        rw [slotMass_eq_blockMass rayM H hH st hpunc η₀ W θ w σ v t D _
          (HeckeInverseAmplification.rowMap_ne_zero _), Finset.sum_coe_sort D w]
        exact h3))
    hh p X₁ X₂ hX₁ hX₂ h21 hl₁ hl₂

/-- **R1**: the selected root energy at every cut `K ∈ [0.500001, 3/4]`. -/
theorem selectedRootEnergy (K : ℝ) (hK1 : (500001/1000000:ℝ) ≤ K) (hK2 : K ≤ 3/4) :
    SelectedRootEnergy K :=
  selectedRootEnergy_of_ord K (ord_of_cap K (cap_proof K hK1 hK2))

end
end QRH.ArviSelectedLeaf
