/-
Reduction of R1 to slot sets of total weight at most `Mcap + 1`.

When the slots weigh more, a sub-block `T'` of weight in `[Mcap + 1 - mesh, Mcap + 1]` is kept and the others are
deleted: each deleted prime slot has square at most `256² LW² Z^w`, and the price is unchanged because
`selExcess` is affine in the slot weight once the slot weight exceeds the row width. The heavy block need not lie
in the kept slots.
-/
import Submissions.arvi_selected_leaf.R1.Swap
import Submissions.sil_density_split_20261026.Density.LeafRows

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
local notation "O" => HeckeFamily.O

/-- R1 for ordered plain lengths and slot sets of weight at most `Mcap + 1` (the heavy block is arbitrary). -/
def SelectedRootEnergyCap (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ smin Mmin Mcap : ℝ, 0 < smin → 0 < Mmin → Mmin ≤ Mcap →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 2 ≤ bΦ →
  ∃ degree : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (T D : Finset α),
  ∀ (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ 33/50) →
    0 ≤ height → (∀ i, |v i| ≤ height) → smin ≤ ∑ i ∈ D, w i → ∑ i ∈ T, w i ≤ Mcap + 1 →
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₂ ≤ X₁ →
    length Z X₁ ≤ 4 → length Z X₂ ≤ 4 →
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : T => primePool rayM H 2 (Z^(w i)))
      (fun (i : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : T => Z^(w i)) X₁ X₂
      (fun z => st.radial.keep z ∧
        Z^(K * ∑ i ∈ D, w i) ≤ blockMass rayM H hH W η₀ st.character θ w σ v t Z D z)
      st.radial.profile st.radial.scale ≤
    C * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
      (1+|t|+height)^degree *
      Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε)

/-- The price is affine in the slot weight above the row width. -/
theorem selExcess_peel (P s s' M : ℝ) (hP : 0 ≤ P) (hs' : M ≤ s') :
    (s - s') + (M + selExcess P s' M) ≤ M + selExcess P s M := by
  unfold selExcess
  have h5 : 0 ≤ max 0 ((M - P)/5) := le_max_left _ _
  have h1 : 0 ≤ P + s' + max 0 ((M - P)/5) - M := by linarith
  rw [max_eq_right h1]
  have h2 : P + s + max 0 ((M - P)/5) - M ≤ max 0 (P + s + max 0 ((M - P)/5) - M) := le_max_right _ _
  linarith

/-- **Reduction to slot sets of bounded weight.** -/
theorem ord_of_cap (K : ℝ) (h : SelectedRootEnergyCap K) : SelectedRootEnergyOrd K := by
  intro ε hε smin Mmin Mcap hsmin hMmin hMcap
  obtain ⟨meshMax, hmeshMax, h⟩ := h ε hε smin Mmin Mcap hsmin hMmin hMcap
  refine ⟨min meshMax 1, lt_min hmeshMax one_pos, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨degree, S, C, hC, hev⟩ := h mesh (hmesh.trans (min_le_left _ _)) α rayM H hH W hW hWs κ
    anchors η₀ bΦ hbΦ
  obtain ⟨LW, hLW⟩ : ∃ LW, ∀ x, ‖W x‖ ≤ LW :=
    hW.continuous.bounded_above_of_compact_support (HasCompactSupport.intro isCompact_Icc
      (fun x hx => by
        by_contra h'
        exact hx (hWs h')))
  have hLW0 : 0 ≤ LW := (norm_nonneg _).trans (hLW 0)
  set cp : ℝ := max 1 (256^2 * LW^2) with hcp
  have hcp1 : 1 ≤ cp := le_max_left _ _
  refine ⟨degree, S, C * cp^(Fintype.card α), by positivity, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro j st hchar hpunc hM1 hM2 T D hDT θ w σ v t height hw hwm hσ1 hσ2 hh hv hsD p X₁ X₂ hX₁ hX₂ h21
    hl₁ hl₂
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := by linarith
  have hmesh1 : mesh ≤ 1 := hmesh.trans (min_le_right _ _)
  have hcpow : 1 ≤ cp^(Fintype.card α) := one_le_pow₀ hcp1
  have hR0 : 0 ≤ QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
      (1+|t|+height)^degree :=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg _) (sq_nonneg _))
      (pow_nonneg (by positivity) _)
  by_cases hcap : ∑ i ∈ T, w i ≤ Mcap + 1
  · have hb := hZ.2 j st hchar hpunc hM1 hM2 T D θ w σ v t height hw hwm hσ1 hσ2 hh hv hsD hcap p X₁ X₂
      hX₁ hX₂ h21 hl₁ hl₂
    refine hb.trans ?_
    have hZp : 0 ≤ Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε) :=
      Real.rpow_nonneg hZ0.le _
    calc C * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
          (1+|t|+height)^degree *
          Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε)
        = C * (QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
          (1+|t|+height)^degree) *
          Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε) := by
          ring
      _ ≤ (C * cp^(Fintype.card α)) * (QuadraticInitialBound.diagonalControl st.radial.profile *
          (p.control S)^2 * (1+|t|+height)^degree) *
          Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε) := by
          apply mul_le_mul_of_nonneg_right _ hZp
          apply mul_le_mul_of_nonneg_right _ hR0
          exact le_mul_of_one_le_right hC.le hcpow
      _ = _ := by ring
  · rw [not_le] at hcap
    obtain ⟨T', hT'T, hlow, hup⟩ := R1.exists_sub_weight w mesh (Mcap + 1) (by linarith) hwm T hcap
    set L : O → Prop := fun z => Z^(K * ∑ i ∈ D, w i) ≤
      blockMass rayM H hH W η₀ st.character θ w σ v t Z D z with hLdef
    let s' := QRH.SilDensitySplit.Density.restrictState st L
    have hu' : s'.puncture = 1 := hpunc
    set E : ℝ := ∏ i ∈ T \ T', (256^2 * LW^2 * Z^(w i)) with hE
    have hslot : ∀ z, s'.radial.keep z →
        s'.radial.profile (‖eisEmbedding z‖^2/s'.radial.scale) ≠ 0 →
        ‖∏ i ∈ T \ T', normalizedSlot s'.character fixedBadMask 1 z (primePool rayM H 2 (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t (Z^(w i))‖^2 ≤ E := by
      intro z _ _
      rw [norm_prod, ← Finset.prod_pow, hE]
      apply Finset.prod_le_prod₀ (fun i _ => sq_nonneg _)
      intro i _
      exact R1.primeSlot_sq_le _ _ _ _ rayM H _ t (Z^(w i)) LW (Real.rpow_pos_of_pos hZ0 _) hLW0
        (fun I _ => R1.annular_coeff_le _ W LW (Z^(w i)) (σ i) (v i) I (Real.rpow_pos_of_pos hZ0 _)
          (by linarith [hσ1 i]) hWs hLW)
    have hdel := SilDensitySplit.CubeFree.energy_partial_delete s' hu' T T' hT'T
      (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) (fun _ => Real.rpow_nonneg hZ0.le _) (p.profile 0) (p.profile 1) t X₁ X₂ E
      (mul_pos hX₁ hX₂).le hslot
    have hb := hZ.2 j st hchar hpunc hM1 hM2 T' D θ w σ v t height hw hwm hσ1 hσ2 hh hv hsD hup p X₁ X₂
      hX₁ hX₂ h21 hl₁ hl₂
    -- the peel factor
    have hEval : E = (256^2 * LW^2)^((T \ T').card) * Z^(∑ i ∈ T \ T', w i) := by
      rw [hE, Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos hZ0]
    have hcardle : (T \ T').card ≤ Fintype.card α := Finset.card_le_univ _
    have hfac : (256^2 * LW^2)^((T \ T').card) ≤ cp^(Fintype.card α) :=
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans (pow_le_pow_right₀ hcp1 hcardle)
    have hsplit : ∑ i ∈ T, w i = ∑ i ∈ T \ T', w i + ∑ i ∈ T', w i :=
      (Finset.sum_sdiff hT'T).symm
    have hMw : st.rowWidth ≤ ∑ i ∈ T', w i := by
      have hw' : st.rowWidth ≤ st.width := by
        unfold NaturalState.width; linarith [st.character_nonneg]
      linarith
    have hP0 : 0 ≤ length Z X₁ + length Z X₂ :=
      add_nonneg (length_nonneg Z X₁ hZ1) (length_nonneg Z X₂ hZ1)
    have hexp := selExcess_peel (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) (∑ i ∈ T', w i)
      st.rowWidth hP0 hMw
    have hdiff : ∑ i ∈ T \ T', w i = ∑ i ∈ T, w i - ∑ i ∈ T', w i := by linarith
    calc energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : T => primePool rayM H 2 (Z^(w i)))
          (fun (i : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
          (fun i : T => Z^(w i)) X₁ X₂ (fun z => st.radial.keep z ∧ L z)
          st.radial.profile st.radial.scale
        ≤ E * energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : T' => primePool rayM H 2 (Z^(w i)))
          (fun (i : T') I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
          (fun i : T' => Z^(w i)) X₁ X₂ (fun z => st.radial.keep z ∧ L z)
          st.radial.profile st.radial.scale := hdel
      _ ≤ E * (C * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
          (1+|t|+height)^degree *
          Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T', w i) st.rowWidth + ε)) :=
          mul_le_mul_of_nonneg_left hb (by rw [hE]; positivity)
      _ = (256^2 * LW^2)^((T \ T').card) * C *
          (QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
            (1+|t|+height)^degree) *
          Z^((∑ i ∈ T \ T', w i) +
            (st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T', w i) st.rowWidth + ε)) := by
          rw [hEval, Real.rpow_add hZ0 (∑ i ∈ T \ T', w i)]
          ring
      _ ≤ cp^(Fintype.card α) * C *
          (QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
            (1+|t|+height)^degree) *
          Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε) := by
          apply mul_le_mul _ _ (Real.rpow_nonneg hZ0.le _) (by positivity)
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hC.le) hR0
          · apply Real.rpow_le_rpow_of_exponent_le hZ1.le
            rw [hdiff]
            linarith
      _ = _ := by ring

end
end QRH.ArviSelectedLeaf
