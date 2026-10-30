/-
R1 at one base `Z`: the energy of the heavy rows of a natural state (ordered plain lengths, slot weight at most
`Mcap + 1`), from the per-root selected norm (`hnormR`) and the reflected class bound (`hrefl`).
-/
import Submissions.arvi_selected_leaf.R1.Final

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
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- The divisor factor. -/
theorem lambda_bound (Z auxCap εd u Dε : ℝ) (k nα : ℕ) (hZ : 1 < Z) (ha : 0 ≤ auxCap) (he : 0 ≤ εd)
    (hk : k ≤ nα) (hdef : εd * (auxCap * (2 + (nα:ℝ))) = u) :
    (max 1 Dε * (Z^auxCap)^εd)^(2 + k) ≤ (max 1 Dε)^(2 + nα) * Z^u := by
  have hZ0 : 0 < Z := by linarith
  have h1 : 1 ≤ max 1 Dε := le_max_left _ _
  have h2 : 1 ≤ (Z^auxCap)^εd := Real.one_le_rpow (Real.one_le_rpow hZ.le ha) he
  have hb1 : 1 ≤ max 1 Dε * (Z^auxCap)^εd := one_le_mul_of_one_le_of_one_le h1 h2
  calc (max 1 Dε * (Z^auxCap)^εd)^(2 + k) ≤ (max 1 Dε * (Z^auxCap)^εd)^(2 + nα) :=
        pow_le_pow_right₀ hb1 (by omega)
    _ = (max 1 Dε)^(2 + nα) * ((Z^auxCap)^εd)^(2 + nα) := mul_pow _ _ _
    _ = (max 1 Dε)^(2 + nα) * Z^u := by
        congr 1
        rw [← Real.rpow_mul hZ0.le, ← Real.rpow_mul_natCast hZ0.le, ← hdef]
        congr 1
        push_cast
        ring

/-- The constant of the reflected route. -/
theorem xi_bound (Z M Mcap u Cscale Ce De : ℝ) (hZ : 1 < Z) (hM0 : 0 ≤ M) (hMc : M ≤ Mcap)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hCe : 0 ≤ Ce) (hDe : 0 ≤ De) :
    Ce * (max 1 (Cscale * Z^M))^(u/(Mcap+1)) * (1 + 2*((Mcap+1) * Real.log Z)) +
      De * (max 1 (Cscale * Z^M))^(2*(u/(Mcap+1))) ≤
    (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) * Z^(2*u) := by
  have hZ0 : 0 < Z := by linarith
  have hMc0 : 0 ≤ Mcap := hM0.trans hMc
  have hMc1 : 0 < Mcap + 1 := by linarith
  set εe := u/(Mcap+1) with hεe
  have hεe0 : 0 ≤ εe := by rw [hεe]; positivity
  have hεe1 : εe ≤ 1 := by rw [hεe, div_le_one hMc1]; linarith
  have hMε : Mcap * εe ≤ u := by
    rw [hεe, mul_div_assoc', div_le_iff₀ hMc1]; nlinarith
  set C1 := max 1 Cscale with hC1
  have hC11 : 1 ≤ C1 := le_max_left _ _
  have hZM : 1 ≤ Z^Mcap := Real.one_le_rpow hZ.le hMc0
  have hR : max 1 (Cscale * Z^M) ≤ C1 * Z^Mcap := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hC11 hZM
    · apply mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hZ.le hMc)
        (Real.rpow_nonneg hZ0.le _) (by linarith)
  have hR0 : 0 ≤ max 1 (Cscale * Z^M) := zero_le_one.trans (le_max_left _ _)
  have hCZ0 : 0 ≤ C1 * Z^Mcap := by positivity
  have hp1 : (max 1 (Cscale * Z^M))^εe ≤ C1 * Z^u := by
    calc (max 1 (Cscale * Z^M))^εe ≤ (C1 * Z^Mcap)^εe := Real.rpow_le_rpow hR0 hR hεe0
      _ = C1^εe * Z^(Mcap * εe) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
      _ ≤ C1 * Z^u := by
          apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hZ.le hMε) (Real.rpow_nonneg hZ0.le _)
            (by linarith)
          calc C1^εe ≤ C1^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hC11 hεe1
            _ = C1 := Real.rpow_one C1
  have hp2 : (max 1 (Cscale * Z^M))^(2*εe) ≤ C1^2 * Z^(2*u) := by
    calc (max 1 (Cscale * Z^M))^(2*εe) ≤ (C1 * Z^Mcap)^(2*εe) := Real.rpow_le_rpow hR0 hR (by positivity)
      _ = C1^(2*εe) * Z^(Mcap * (2*εe)) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
      _ ≤ C1^2 * Z^(2*u) := by
          apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith))
            (Real.rpow_nonneg hZ0.le _) (by positivity)
          calc C1^(2*εe) ≤ C1^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hC11 (by linarith)
            _ = C1^2 := by norm_cast
  have hlog : Real.log Z ≤ Z^u / u := Real.log_le_rpow_div hZ0.le hu0
  have hlog0 : 0 ≤ Real.log Z := (Real.log_pos hZ).le
  have hZu1 : 1 ≤ Z^u := Real.one_le_rpow hZ.le hu0.le
  have hZ2u : Z^(2*u) = Z^u * Z^u := by rw [← Real.rpow_add hZ0]; ring_nf
  have hZu2 : Z^u ≤ Z^(2*u) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hp1' : 0 ≤ (max 1 (Cscale * Z^M))^εe := Real.rpow_nonneg hR0 _
  have hA : Ce * (max 1 (Cscale * Z^M))^εe * (1 + 2*((Mcap+1) * Real.log Z)) ≤
      Ce * C1 * (1 + 2*(Mcap+1)/u) * Z^(2*u) := by
    have hlogb : 1 + 2*((Mcap+1) * Real.log Z) ≤ 1 + 2*(Mcap+1)*(Z^u/u) := by nlinarith
    calc Ce * (max 1 (Cscale * Z^M))^εe * (1 + 2*((Mcap+1) * Real.log Z))
        ≤ Ce * (C1 * Z^u) * (1 + 2*(Mcap+1)*(Z^u/u)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hp1 hCe) hlogb (by positivity) (by positivity)
      _ = Ce * C1 * (Z^u + 2*(Mcap+1)/u * (Z^u * Z^u)) := by ring
      _ = Ce * C1 * (Z^u + 2*(Mcap+1)/u * Z^(2*u)) := by rw [hZ2u]
      _ ≤ Ce * C1 * (Z^(2*u) + 2*(Mcap+1)/u * Z^(2*u)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = Ce * C1 * (1 + 2*(Mcap+1)/u) * Z^(2*u) := by ring
  have hB : De * (max 1 (Cscale * Z^M))^(2*εe) ≤ De * C1^2 * Z^(2*u) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hp2 hDe
  calc _ ≤ Ce * C1 * (1 + 2*(Mcap+1)/u) * Z^(2*u) + De * C1^2 * Z^(2*u) := add_le_add hA hB
    _ = _ := by ring


/-- The class constant in closed form. -/
theorem A_bound (diag Kn Knorm Zu Λ L₀ Γ Γc Z2u T2 c₁ c₂ ctl msp M₀ : ℝ) (hdiag : 0 ≤ diag)
    (hKn : Kn = Knorm * Zu) (hKnorm : 0 ≤ Knorm) (hZu : 0 ≤ Zu) (hΛ : Λ ≤ L₀ * Zu) (hΛ0 : 0 ≤ Λ)
    (hL₀ : 0 ≤ L₀) (hΓ : Γ ≤ Γc * Z2u * T2) (hΓ0 : 0 ≤ Γ) (hΓc : 0 ≤ Γc) (hZ2u : 0 ≤ Z2u)
    (hT2 : 0 ≤ T2) (hctl : c₁ * c₂ = ctl) (hmsp : msp ≤ M₀) (hmsp0 : 0 ≤ msp) :
    diag * (2*Kn) * Λ * (Γ * c₁^2 * c₂^2 * msp) ≤
      (2 * Knorm * L₀ * Γc * M₀) * diag * ctl^2 * T2 * (Zu * Zu * Z2u) := by
  have hX : 0 ≤ diag * ctl^2 := mul_nonneg hdiag (sq_nonneg _)
  have hK2 : 0 ≤ 2 * Knorm * Zu := by positivity
  calc diag * (2*Kn) * Λ * (Γ * c₁^2 * c₂^2 * msp)
      = (2 * Knorm * Zu) * Λ * Γ * msp * (diag * ctl^2) := by rw [hKn, ← hctl]; ring
    _ ≤ (2 * Knorm * Zu) * (L₀ * Zu) * Γ * msp * (diag * ctl^2) := by
        apply mul_le_mul_of_nonneg_right _ hX
        apply mul_le_mul_of_nonneg_right _ hmsp0
        apply mul_le_mul_of_nonneg_right _ hΓ0
        exact mul_le_mul_of_nonneg_left hΛ hK2
    _ ≤ (2 * Knorm * Zu) * (L₀ * Zu) * (Γc * Z2u * T2) * msp * (diag * ctl^2) := by
        apply mul_le_mul_of_nonneg_right _ hX
        apply mul_le_mul_of_nonneg_right _ hmsp0
        exact mul_le_mul_of_nonneg_left hΓ (by positivity)
    _ ≤ (2 * Knorm * Zu) * (L₀ * Zu) * (Γc * Z2u * T2) * M₀ * (diag * ctl^2) := by
        apply mul_le_mul_of_nonneg_right _ hX
        exact mul_le_mul_of_nonneg_left hmsp (by positivity)
    _ = _ := by ring

/-- The final combination. -/
theorem final_combine (Ssum A Br CBZ CB CA E u ε diag ctl T2 Z : ℝ) (hZ : 1 < Z) (hu : 0 ≤ u)
    (h6u : 6*u ≤ ε) (hSsum : Ssum ≤ (9/4) * A * Br) (hBr : Br ≤ CBZ * Z^(E + 2*u)) (hA0 : 0 ≤ A)
    (hA : A ≤ CA * diag * ctl^2 * T2 * Z^(4*u)) (hCB : CBZ ≤ CB) (hCBZ0 : 0 ≤ CBZ)
    (hrest : 0 ≤ CA * diag * ctl^2 * T2) :
    Ssum ≤ ((9/4) * CA) * CB * diag * ctl^2 * T2 * Z^(E + ε) := by
  have hZ0 : 0 < Z := by linarith
  have hZE : 0 ≤ Z^(E + 2*u) := Real.rpow_nonneg hZ0.le _
  calc Ssum ≤ (9/4) * A * Br := hSsum
    _ ≤ (9/4) * A * (CBZ * Z^(E + 2*u)) := mul_le_mul_of_nonneg_left hBr (by positivity)
    _ ≤ (9/4) * (CA * diag * ctl^2 * T2 * Z^(4*u)) * (CB * Z^(E + 2*u)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul_of_nonneg_right hCB hZE) (by positivity) (by positivity)
    _ = ((9/4) * CA) * CB * diag * ctl^2 * T2 * (Z^(4*u) * Z^(E + 2*u)) := by ring
    _ = ((9/4) * CA) * CB * diag * ctl^2 * T2 * Z^(E + 6*u) := by
        rw [← Real.rpow_add hZ0]; ring_nf
    _ ≤ ((9/4) * CA) * CB * diag * ctl^2 * T2 * Z^(E + ε) := by
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
        have hCB0 : 0 ≤ CB := hCBZ0.trans hCB
        rw [show ((9/4) * CA) * CB * diag * ctl^2 * T2 = (9/4) * CB * (CA * diag * ctl^2 * T2) by ring]
        exact mul_nonneg (mul_nonneg (by norm_num) hCB0) hrest

set_option maxHeartbeats 40000000 in
/-- **R1 at one base.** -/
theorem cap_body (K ε Mmin Mcap u auxCap εd Knorm cη Cscale Ce De La Csc C₆ LW bΦ Z t height : ℝ)
    (n : ℕ) (Se S : Finset (ℕ×ℕ))
    (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hMmin : 0 < Mmin) (hu0 : 0 < u) (hu1 : u ≤ 1/20) (huε : u ≤ ε/20)
    (hauxCap : 4*(Mcap+1) + 31 ≤ auxCap)
    {α : Type} [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O ⧸ rayM)ˣ)
    (hbΦ : 2 ≤ bΦ) (hεd : 0 < εd) (hεdDef : εd * (auxCap * (2 + (Fintype.card α : ℝ))) = u)
    (hKnorm : 0 < Knorm)
    (hCscale : Cscale = cη * ((Ideal.span {fixedBadMask}).absNorm : ℝ) *
      ((Ideal.span {(72:O)}).absNorm : ℝ) * bΦ)
    (hCs : 0 < Cscale) (hCe : 0 < Ce) (hDe : 0 < De) (hLa : 1 ≤ La) (hLW : 0 ≤ LW)
    (hS0 : ((0:ℕ),(0:ℕ)) ∈ S) (hSeS : Se ⊆ S) (hCsc : 1 ≤ Csc)
    (hscaleS : ∀ (V : 𝓢(ℝ,ℂ)) (x : ℝ), ‖CenteredMomentScaleSupremum.scaleTest (V : ℝ → ℂ) 1 x‖ ≤ Csc * sourceControl S V)
    (hC₆ : 0 < C₆)
    (hsum : ∀ (A₀ Dd Rr Q Y₀ B η : ℝ), 0 ≤ A₀ → 0 ≤ Dd → 0 ≤ Rr → 0 ≤ Q → 0 ≤ Y₀ → 0 ≤ B → 0 < η →
      η ≤ 4 → ∀ (R : Finset HeckeInverseAmplification.NonzeroIdeal)
        (f : HeckeInverseAmplification.NonzeroIdeal → ℝ),
        (∀ r ∈ R, R1.rootNorm r ^ (6:ℝ) ≤ B) →
        (∀ r ∈ R, f r ≤ A₀ * (Y₀ + B * R1.rootNorm r ^ (-(6:ℝ)) +
          min Dd (Rr * max 1 (Q * R1.rootNorm r ^ (-(5:ℝ)))))) →
        ∑ r ∈ R, f r ≤ A₀ * ((Y₀ + Rr) * (R1.rootZeta (1+η) * B^((1+η)/6)) + C₆ * B +
          R1.rootZeta (1+η) * (Dd^(1-(1+η)/5) * (Rr*Q)^((1+η)/5))))
    (hZ1 : 1 < Z) (hZbig : (9/4)^2 * 2^(Fintype.card α) ≤ Z)
    (hrefl : R1.ReflectedClassAt n Se Ce De La (u/(Mcap+1)) Cscale u Mcap Z)
    (st : NaturalState Z 0 bΦ) (hpunc : st.puncture = 1)
    (hηmod : ((st.character.modulus.absNorm : ℕ) : ℝ) ≤ cη) (hMlow : Mmin ≤ st.rowWidth)
    (hMup : st.width ≤ Mcap)
    (T : Finset α) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) (hsT : ∑ i ∈ T, w i ≤ Mcap + 1)
    (β : T → Ideal O → ℂ) (hβ : ∀ (i : T) (I : Ideal O), ‖β i I‖ ≤ LW)
    (heavy : O → Prop)
    (hnormR : ∀ (r : HeckeInverseAmplification.NonzeroIdeal)
      (cores : Finset HeckeInverseAmplification.FreeRow) (Y : ℝ),
      Z^(Mmin/20) ≤ Y → Y ≤ bΦ * Z^st.rowWidth →
      (∀ u ∈ cores, ProbeHighRowFamily.rowNorm u ≤ Y ∧
        ∃ _ : st.radial.keep (HeckeInverseAmplification.rowMap (u,r)),
        st.radial.profile (‖eisEmbedding (HeckeInverseAmplification.rowMap (u,r))‖^2/st.radial.scale) ≠ 0 ∧
        heavy (HeckeInverseAmplification.rowMap (u,r))) →
      SelectedAllSourceNormBound (cores.image Subtype.val) Y K (Knorm * Z^u) (Z^auxCap))
    (hh : 0 ≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (h21 : X₂ ≤ X₁)
    (hl₁ : length Z X₁ ≤ 4) (hl₂ : length Z X₂ ≤ 4) :
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : T => primePool rayM H 2 (Z^(w i))) β (fun i : T => Z^(w i)) X₁ X₂
      (fun z => st.radial.keep z ∧ heavy z) st.radial.profile st.radial.scale ≤
    ((9/4) * (2 * Knorm * (max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd))^(2 + Fintype.card α) *
        ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
          (128 * La^2 * (128*(9/4))) * Csc^2) * (max 1 (256 * LW^2))^(Fintype.card α)) *
      (R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + (9/4) * 2^(Fintype.card α)) + C₆ * bΦ +
        R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * ((9/4) * 2^(Fintype.card α)))) *
      QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
      (1+|t|+height)^(2*n) *
      Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε) := by
  ------------------------------------------------------------------ basic facts
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ1
  have hM0 : 0 ≤ st.rowWidth := st.row_nonneg
  have hMc : st.rowWidth ≤ Mcap := by
    have : st.rowWidth ≤ st.width := by
      unfold NaturalState.width; linarith only [st.character_nonneg]
    exact this.trans hMup
  have hMcap0 : 0 ≤ Mcap := hM0.trans hMc
  have hU : st.radial.scale = Z^st.rowWidth := st.scale_eq
  have hUpos : 0 < st.radial.scale := st.radial.scale_pos
  have hm : (fixedBadMask : O) ≠ 0 := fixedBadMask_ne_zero
  have hmLam : λ₀ ∣ (fixedBadMask : O) := dvd_mul_right _ _
  have hm2 : (2:O) ∣ (fixedBadMask : O) := dvd_mul_left _ _
  have hP : ∀ i : T, 0 < Z^(w i) := fun i => Real.rpow_pos_of_pos hZ0 _
  have hZw : ∀ i : T, 1 ≤ Z^(w i) := fun i => Real.one_le_rpow hZ1.le (hw i)
  have hbΦ0 : 0 < bΦ := by linarith only [hbΦ]
  have hℓ₁0 : 0 ≤ length Z X₁ := length_nonneg Z X₁ hZ1
  have hℓ₂0 : 0 ≤ length Z X₂ := length_nonneg Z X₂ hZ1
  have hℓ : length Z X₂ ≤ length Z X₁ := by
    unfold length
    exact Real.logb_le_logb_of_le hZ1 (zero_lt_one.trans_le (le_max_left _ _)) (max_le_max le_rfl h21)
  have hZℓ₁ : Z^(length Z X₁) = max 1 X₁ := R1.rpow_length Z X₁ hZ1
  have hZℓ₂ : Z^(length Z X₂) = max 1 X₂ := R1.rpow_length Z X₂ hZ1
  have hs0 : 0 ≤ ∑ i ∈ T, w i := Finset.sum_nonneg (fun i _ => hw i)
  ------------------------------------------------------------------ the energy as a radial energy
  obtain ⟨keep'', hk⟩ : ∃ k : O → Prop, k = fun z => (st.radial.keep z ∧ heavy z) ∧
      ‖eisEmbedding z‖^2 ≤ bΦ * st.radial.scale := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : O → ℂ, F = fun z =>
      HeckeDyadic.polynomial (R1.radRow st.character fixedBadMask z hm hmLam hm2) false (p.profile 0) X₁ 0 t *
      HeckeDyadic.polynomial (R1.radRow st.character fixedBadMask z hm hmLam hm2) false (p.profile 1) X₂ 0 t *
      ∏ i : T, normalizedSlot st.character fixedBadMask 1 z (primePool rayM H 2 (Z^(w i))) (β i) t
        (Z^(w i)) := ⟨_, rfl⟩
  have hnz'' : ∀ z, keep'' z → z ≠ 0 := by
    intro z hz; rw [hk] at hz; exact st.row_ne_zero z hz.1.1
  have hmask : st.mask = fixedBadMask * idealGenerator 1 := by rw [NaturalState.mask, hpunc]
  have e1 : energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : T => primePool rayM H 2 (Z^(w i))) β (fun i : T => Z^(w i)) X₁ X₂
      (fun z => st.radial.keep z ∧ heavy z) st.radial.profile st.radial.scale =
      CenteredMomentOriginalRadialComparison.radialEnergy F keep'' st.radial.profile st.radial.scale := by
    rw [hmask, unit_puncture_energy (keep := fun z => st.radial.keep z ∧ heavy z)
      (hz := fun z h => st.row_ne_zero z h.1),
      energy_support_restrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ bΦ hUpos st.radial_support, hk, hF]
    exact R1.energy_eq_radial st.character fixedBadMask hm hmLam hm2 _ _ _ _ _ t X₁ X₂ hX₁ hX₂ hP
      (fun z => (st.radial.keep z ∧ heavy z) ∧ ‖eisEmbedding z‖^2 ≤ bΦ * st.radial.scale)
      (fun z h => st.row_ne_zero z h.1.1) _ _
  rw [e1]
  ------------------------------------------------------------------ the root split
  obtain ⟨Dk, hDk⟩ : ∃ D' : Finset O,
      D' = ConcretePrimeRowBridge.rowNormDisk ⌊max 0 (bΦ * st.radial.scale)⌋₊ := ⟨_, rfl⟩
  obtain ⟨Pk, hPk⟩ : ∃ P' : O → Prop,
      P' = fun z => keep'' z ∧ st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R' : Finset HeckeInverseAmplification.NonzeroIdeal,
      R' = (Dk.filter Pk).image R1.rootOf := ⟨_, rfl⟩
  have hDkmem : ∀ z, keep'' z → z ∈ Dk := by
    intro z hz
    have hz' := hz
    rw [hk] at hz'
    rw [hDk, TruncatedPrincipalPoisson.mem_rowNormDisk_floor (le_max_left _ _)]
    exact ⟨hnz'' z hz, hz'.2.trans (le_max_right _ _)⟩
  have hRmem : ∀ z, keep'' z → st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
      R1.rootOf z ∈ R := by
    intro z hz hΦz
    rw [hR]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hDkmem z hz, by rw [hPk]; exact ⟨hz, hΦz⟩⟩)
  rw [R1.radial_root_split F keep'' st.radial.profile st.radial.scale bΦ hUpos st.radial_support hnz''
    R1.rootOf R hRmem]
  ------------------------------------------------------------------ constants of the classes
  obtain ⟨Kn, hKn⟩ : ∃ x : ℝ, x = Knorm * Z^u := ⟨_, rfl⟩
  have hKn0 : 0 ≤ Kn := by rw [hKn]; positivity
  obtain ⟨Bs, hBs⟩ : ∃ f : T → ℝ, f = fun i : T => 2 * Z^(w i) := ⟨_, rfl⟩
  obtain ⟨ms, hmsd⟩ : ∃ f : T → ℝ, f = fun _ : T => 256 * LW^2 := ⟨_, rfl⟩
  have hprodB : ∏ i : T, Bs i = 2^(Fintype.card T) * Z^(∑ i ∈ T, w i) := by
    rw [hBs]; exact prod_slot_bounds T w Z hZ0
  have hprodm : ∏ i : T, ms i = (256 * LW^2)^(Fintype.card T) := by
    rw [hmsd, Finset.prod_const, Finset.card_univ]
  have hcardT : Fintype.card T ≤ Fintype.card α := by
    rw [Fintype.card_coe]; exact Finset.card_le_univ T
  -- the lengths
  obtain ⟨cR, hcR⟩ : ∃ x : ℝ, x = 9/4 * 2^(Fintype.card T) := ⟨_, rfl⟩
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  have hcRle : cR ≤ (9/4) * 2^(Fintype.card α) := by
    rw [hcR]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcardT) (by norm_num)
  have hRrB : max 1 (9/4 * X₂) * ∏ i : T, Bs i ≤ cR * Z^(length Z X₂ + ∑ i ∈ T, w i) := by
    rw [hprodB, Real.rpow_add hZ0, hZℓ₂, hcR]
    have h1 := R1.max_one_mul_le (9/4) X₂ (by norm_num)
    calc max 1 (9/4 * X₂) * (2^(Fintype.card T) * Z^(∑ i ∈ T, w i))
        ≤ (9/4 * max 1 X₂) * (2^(Fintype.card T) * Z^(∑ i ∈ T, w i)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 9/4 * 2^(Fintype.card T) * (max 1 X₂ * Z^(∑ i ∈ T, w i)) := by ring
  obtain ⟨Xd, hXd⟩ : ∃ x : ℝ, x = max 1 (9/4*X₁) * (max 1 (9/4*X₂) * ∏ i, Bs i) := ⟨_, rfl⟩
  have hXdD : Xd ≤ 9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i) := by
    rw [hXd, add_assoc, Real.rpow_add hZ0, hZℓ₁]
    have h1 := R1.max_one_mul_le (9/4) X₁ (by norm_num)
    have h0 : 0 ≤ max 1 (9/4 * X₂) * ∏ i : T, Bs i := by
      rw [hprodB]; have := le_max_left (1:ℝ) (9/4 * X₂); positivity
    calc max 1 (9/4 * X₁) * (max 1 (9/4 * X₂) * ∏ i : T, Bs i)
        ≤ (9/4 * max 1 X₁) * (cR * Z^(length Z X₂ + ∑ i ∈ T, w i)) :=
          mul_le_mul h1 hRrB h0 (by positivity)
      _ = 9/4 * cR * (max 1 X₁ * Z^(length Z X₂ + ∑ i ∈ T, w i)) := by ring
  have hXdmax : Xd ≤ Z^auxCap := by
    refine hXdD.trans ?_
    have hc : 9/4 * cR ≤ Z := by
      calc 9/4 * cR ≤ 9/4 * ((9/4) * 2^(Fintype.card α)) := mul_le_mul_of_nonneg_left hcRle (by norm_num)
        _ = (9/4)^2 * 2^(Fintype.card α) := by ring
        _ ≤ Z := hZbig
    have he : length Z X₁ + length Z X₂ + ∑ i ∈ T, w i ≤ Mcap + 9 := by linarith only [hl₁, hl₂, hsT]
    calc 9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i) ≤ Z * Z^(Mcap + 9) :=
          mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hZ1.le he) (Real.rpow_nonneg hZ0.le _)
            hZ0.le
      _ = Z^(Mcap + 10) := by
          rw [show Mcap + 10 = 1 + (Mcap + 9) by ring, Real.rpow_add hZ0 1 (Mcap + 9), Real.rpow_one]
      _ ≤ Z^auxCap := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hauxCap, hMcap0])
  have hXd1 : 1 ≤ Xd := by
    rw [hXd]
    have h3 : 1 ≤ ∏ i : T, Bs i := by
      rw [hprodB]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
        (Real.one_le_rpow hZ1.le hs0)
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _)
      (one_le_mul_of_one_le_of_one_le (le_max_left _ _) h3)
  -- the divisor factor
  obtain ⟨β₀, hβ₀⟩ : ∃ x : ℝ, x = max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd) *
      (Z^auxCap)^εd := ⟨_, rfl⟩
  have hβ₀D : ∀ X : ℝ, 1 ≤ X → X ≤ Z^auxCap →
      Qrh.JointDetector.idealDivisorConstant εd hεd * X^εd ≤ β₀ := by
    intro X hX1 hXm
    rw [hβ₀]
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow (zero_le_one.trans hX1) hXm hεd.le)
      (Real.rpow_nonneg (zero_le_one.trans hX1) _) (zero_le_one.trans (le_max_left _ _))
  have hβ₀1 : 1 ≤ β₀ := by
    rw [hβ₀]
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _)
      (Real.one_le_rpow (Real.one_le_rpow hZ1.le (by linarith only [hauxCap, hMcap0])) hεd.le)
  have hD0 : 0 ≤ Qrh.JointDetector.idealDivisorConstant εd hεd :=
    (Qrh.JointDetector.idealDivisorConstant_pos εd hεd).le
  obtain ⟨Λ, hΛ⟩ : ∃ x : ℝ, x = β₀^(2 + Fintype.card T) := ⟨_, rfl⟩
  have hΛk : ∀ X : ℝ, 1 ≤ X → X ≤ Z^auxCap → ∀ k, k ≤ 2 + Fintype.card T →
      (Qrh.JointDetector.idealDivisorConstant εd hεd * X^εd)^k ≤ Λ := by
    intro X hX1 hXm k hk
    rw [hΛ]
    have h0 : 0 ≤ Qrh.JointDetector.idealDivisorConstant εd hεd * X^εd :=
      mul_nonneg hD0 (Real.rpow_nonneg (zero_le_one.trans hX1) _)
    exact (pow_le_pow_left₀ h0 (hβ₀D X hX1 hXm) k).trans (pow_le_pow_right₀ hβ₀1 hk)
  ------------------------------------------------------------------ the common class constant
  obtain ⟨Rcap, hRcap⟩ : ∃ x : ℝ, x = max 1 (Cscale * Z^st.rowWidth) := ⟨_, rfl⟩
  have hRcap1 : 1 ≤ Rcap := by rw [hRcap]; exact le_max_left _ _
  have hlogZ : 0 ≤ Real.log Z := (Real.log_pos hZ1).le
  obtain ⟨Ξ, hΞ⟩ : ∃ x : ℝ, x = Ce * Rcap^(u/(Mcap+1)) * (1 + 2*((Mcap+1) * Real.log Z)) +
      De * Rcap^(2*(u/(Mcap+1))) := ⟨_, rfl⟩
  have hΞ0 : 0 ≤ Ξ := by
    rw [hΞ]
    have : 0 ≤ Rcap^(u/(Mcap+1)) := Real.rpow_nonneg (zero_le_one.trans hRcap1) _
    have : 0 ≤ Rcap^(2*(u/(Mcap+1))) := Real.rpow_nonneg (zero_le_one.trans hRcap1) _
    positivity
  obtain ⟨Γ, hΓ⟩ : ∃ x : ℝ, x = ((128*(9/4))^2 + Ξ * (128 * La^2 * (128*(9/4))) * Csc^2) *
      (1+‖t‖)^(2*n) := ⟨_, rfl⟩
  have hT21 : 1 ≤ (1+‖t‖)^(2*n) := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg t))
  have hΓ1 : (128*(9/4):ℝ)^2 ≤ Γ := by
    rw [hΓ]
    have h0 : 0 ≤ Ξ * (128 * La^2 * (128*(9/4))) * Csc^2 := by positivity
    calc (128*(9/4):ℝ)^2 = (128*(9/4))^2 * 1 := (mul_one _).symm
      _ ≤ ((128*(9/4))^2 + Ξ * (128 * La^2 * (128*(9/4))) * Csc^2) * (1+‖t‖)^(2*n) :=
        mul_le_mul (le_add_of_nonneg_right h0) hT21 zero_le_one (by positivity)
  have hΓ2 : Ξ * (1+‖t‖)^(2*n) * (128 * La^2 * (128*(9/4)) * Csc^2) ≤ Γ := by
    rw [hΓ]
    have h0 : 0 ≤ (128*(9/4):ℝ)^2 := by positivity
    calc Ξ * (1+‖t‖)^(2*n) * (128 * La^2 * (128*(9/4)) * Csc^2)
        = (Ξ * (128 * La^2 * (128*(9/4))) * Csc^2) * (1+‖t‖)^(2*n) := by ring
      _ ≤ ((128*(9/4))^2 + Ξ * (128 * La^2 * (128*(9/4))) * Csc^2) * (1+‖t‖)^(2*n) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h0) (by positivity)
  have hΓ0 : 0 ≤ Γ := le_trans (by positivity) hΓ1
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = sourceControl S (p.profile 0) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ x : ℝ, x = sourceControl S (p.profile 1) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact sourceControl_nonneg _ _
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; exact sourceControl_nonneg _ _
  have hms0 : 0 ≤ ∏ i : T, ms i := by rw [hprodm]; positivity
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact pow_nonneg (zero_le_one.trans hβ₀1) _
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = QuadraticInitialBound.diagonalControl st.radial.profile * (2*Kn) * Λ *
      (Γ * c₁^2 * c₂^2 * ∏ i : T, ms i) := ⟨_, rfl⟩
  have hdiag0 := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hc₁b : ∀ x, ‖(p.profile 0 : ℝ → ℂ) x‖ ≤ c₁ := by rw [hc₁]; exact norm_le_control S hS0 _
  have hc₂b : ∀ x, ‖(p.profile 1 : ℝ → ℂ) x‖ ≤ c₂ := by rw [hc₂]; exact norm_le_control S hS0 _
  have hSl : Se.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 0) ≤ c₁ := by
    rw [hc₁]; exact control_mono S Se hSeS _
  have hsc : ∀ (k : Fin 2) (x : ℝ),
      ‖CenteredMomentScaleSupremum.scaleTest (p.profile 1 : ℝ → ℂ) k x‖ ≤ Csc * c₂ := by
    intro k x
    fin_cases k
    · simp only [CenteredMomentScaleSupremum.scaleTest, Fin.zero_eta, ite_true]
      exact (hc₂b x).trans (le_mul_of_one_le_left hc₂0 hCsc)
    · rw [hc₂]; exact hscaleS (p.profile 1) x
  ------------------------------------------------------------------ the bound of each class
  have hroot : ∀ r ∈ R, CenteredMomentOriginalRadialComparison.radialEnergy F
      (fun z => keep'' z ∧ R1.rootOf z = r) st.radial.profile st.radial.scale ≤
      (9/4) * A * (Z^(Mmin/20) + (bΦ * Z^st.rowWidth) * R1.rootNorm r ^ (-(6:ℝ)) +
        min (9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i))
          (cR * Z^(length Z X₂ + ∑ i ∈ T, w i) *
            max 1 (Z^(st.rowWidth - length Z X₁ + u) * R1.rootNorm r ^ (-(5:ℝ))))) := by
    intro r _
    have hNr1 := R1.rootNorm_ge_one r
    have hNr0 := R1.rootNorm_pos r
    obtain ⟨g, hg⟩ : ∃ g : O, g = idealGenerator r.val := ⟨_, rfl⟩
    have hg0 : g ≠ 0 := by rw [hg]; exact idealGenerator_ne_zero r.val r.property
    obtain ⟨cores, hcores⟩ : ∃ c : Finset HeckeInverseAmplification.FreeRow,
        c = R1.classCores Dk Pk r := ⟨_, rfl⟩
    have hcover : ∀ z, (keep'' z ∧ R1.rootOf z = r) →
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
        ∃ u ∈ cores.image Subtype.val, z = u * g^6 := by
      intro z hz hΦz
      obtain ⟨u', hu', hzu⟩ := R1.classCores_cover Dk Pk r z (hnz'' z hz.1) (hDkmem z hz.1)
        (by rw [hPk]; exact ⟨hz.1, hΦz⟩) hz.2
      refine ⟨u'.val, Finset.mem_image_of_mem _ (by rw [hcores]; exact hu'), ?_⟩
      rw [hzu, hg]; rfl
    have hnzc : ∀ u ∈ cores.image Subtype.val, u * g^6 ≠ 0 := by
      intro u hu
      obtain ⟨u', _, rfl⟩ := Finset.mem_image.mp hu
      rw [hg]; exact HeckeInverseAmplification.rowMap_ne_zero (u', r)
    -- the selected norm of the class
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ,
        Y = max (Z^(Mmin/20)) (bΦ * st.radial.scale * R1.rootNorm r ^ (-(6:ℝ))) := ⟨_, rfl⟩
    have hY0 : 0 ≤ Y := by rw [hY]; exact le_max_of_le_left (Real.rpow_nonneg hZ0.le _)
    have h60 : 0 ≤ R1.rootNorm r ^ (-(6:ℝ)) := Real.rpow_nonneg hNr0.le _
    have hnorm : SelectedAllSourceNormBound (cores.image Subtype.val) Y K Kn (Z^auxCap) := by
      rw [hKn]
      apply hnormR r cores Y (by rw [hY]; exact le_max_left _ _)
      · rw [hY]
        apply max_le
        · calc Z^(Mmin/20) ≤ Z^st.rowWidth :=
                Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hMlow, hMmin])
            _ ≤ bΦ * Z^st.rowWidth := le_mul_of_one_le_left (Real.rpow_nonneg hZ0.le _) (by linarith only [hbΦ])
        · rw [← hU]
          have h6 : R1.rootNorm r ^ (-(6:ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hNr1 (by norm_num)
          have hbU : 0 ≤ bΦ * st.radial.scale := by positivity
          calc bΦ * st.radial.scale * R1.rootNorm r ^ (-(6:ℝ)) ≤ bΦ * st.radial.scale * 1 :=
                mul_le_mul_of_nonneg_left h6 hbU
            _ = bΦ * st.radial.scale := mul_one _
      · intro u hu
        rw [hcores, R1.mem_classCores, hPk] at hu
        obtain ⟨_, hku, hΦu⟩ := hu
        have hku' := hku
        rw [hk] at hku'
        refine ⟨?_, hku'.1.1, hΦu, hku'.1.2⟩
        rw [hY]
        refine le_trans ?_ (le_max_right _ _)
        have hN : ((Ideal.span {HeckeInverseAmplification.rowMap (u, r)}).absNorm : ℝ) =
            ((Ideal.span {u.val}).absNorm : ℝ) * (r.val.absNorm : ℝ)^6 := R1.absNorm_rowMap (u, r)
        have hE := ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span
          (HeckeInverseAmplification.rowMap (u, r))
        have hb := hku'.2
        rw [hE, hN] at hb
        have hN6 : (r.val.absNorm : ℝ)^6 * R1.rootNorm r ^ (-(6:ℝ)) = 1 := by
          have : (r.val.absNorm : ℝ)^6 = R1.rootNorm r ^ (6:ℝ) := by
            unfold R1.rootNorm; rw [← Real.rpow_natCast]; norm_num
          rw [this, ← Real.rpow_add hNr0]; norm_num
        show ((Ideal.span {u.val}).absNorm : ℝ) ≤ bΦ * st.radial.scale * R1.rootNorm r ^ (-(6:ℝ))
        calc ((Ideal.span {u.val}).absNorm : ℝ)
            = ((Ideal.span {u.val}).absNorm : ℝ) * (r.val.absNorm : ℝ)^6 * R1.rootNorm r ^ (-(6:ℝ)) := by
              rw [mul_assoc, hN6, mul_one]
          _ ≤ bΦ * st.radial.scale * R1.rootNorm r ^ (-(6:ℝ)) := mul_le_mul_of_nonneg_right hb h60
    -- the slots of the class
    have hB : ∀ i : T, (R1.slotPoly st.character fixedBadMask g (primePool rayM H 2 (Z^(w i))) (β i) t
        (Z^(w i))).NormLe (Bs i) ∧ 1 ≤ Bs i := by
      intro i; rw [hBs]
      exact R1.primeSlot_normLe st.character fixedBadMask g rayM H (β i) t (Z^(w i)) (by linarith only [hZw i])
    have hms : ∀ i : T, (R1.slotPoly st.character fixedBadMask g (primePool rayM H 2 (Z^(w i))) (β i) t
        (Z^(w i))).mass ≤ ms i := by
      intro i; rw [hmsd]
      exact R1.primeSlot_mass_le st.character fixedBadMask g rayM H (β i) t (Z^(w i)) LW (hP i)
        (fun I _ => hβ i I)
    have hYb : Y ≤ Z^(Mmin/20) + (bΦ * Z^st.rowWidth) * R1.rootNorm r ^ (-(6:ℝ)) := by
      rw [hY, ← hU]
      apply max_le
      · have : 0 ≤ bΦ * st.radial.scale * R1.rootNorm r ^ (-(6:ℝ)) := by positivity
        exact le_add_of_nonneg_right this
      · have : 0 ≤ Z^(Mmin/20) := Real.rpow_nonneg hZ0.le _
        exact le_add_of_nonneg_left this
    -- the direct bound
    have hfd : CenteredMomentOriginalRadialComparison.radialEnergy F
        (fun z => keep'' z ∧ R1.rootOf z = r) st.radial.profile st.radial.scale ≤ A * (Xd + Y) := by
      have hdir := R1.root_bound_direct (cores.image Subtype.val) Y K Kn (Z^auxCap) Xd hY0 hK0 hK1 hnorm
        εd hεd st.character fixedBadMask g hm hmLam hm2 (fun z => keep'' z ∧ R1.rootOf z = r)
        st.radial.profile st.radial.scale st.radial.nonneg hcover hnzc (p.profile 0) (p.profile 1)
        (p.support 0) (p.support 1) c₁ c₂ hc₁b hc₂b (fun i : T => primePool rayM H 2 (Z^(w i))) β
        (fun i : T => Z^(w i)) t Bs ms hB hms X₁ X₂ hX₁ hX₂ (le_of_eq hXd.symm) hXdmax Λ
        (hΛk Xd hXd1 hXdmax _ le_rfl)
      rw [hF]
      refine hdir.trans ?_
      rw [hA]
      exact weaken_lead _ _ _ _ _ _ _ (by positivity) hΓ1 (sq_nonneg _) (sq_nonneg _) hms0 (by linarith only [hXd1, hY0])
    by_cases hX₁1 : 1 ≤ X₁
    · -- the reflected bound
      have hℓ₁eq : length Z X₁ = Real.logb Z X₁ := by unfold length; rw [max_eq_right hX₁1]
      obtain ⟨Mr, hMr⟩ : ∃ x : ℝ, x = st.rowWidth - 5 * Real.logb Z (R1.rootNorm r) := ⟨_, rfl⟩
      have hlogN : 0 ≤ Real.logb Z (R1.rootNorm r) := Real.logb_nonneg hZ1 hNr1
      have hlogX : 0 ≤ Real.logb Z X₁ := Real.logb_nonneg hZ1 hX₁1
      have hMrM : Mr ≤ st.rowWidth := by rw [hMr]; linarith only [hlogN]
      have hZMr : Z^Mr = Z^st.rowWidth * R1.rootNorm r ^ (-(5:ℝ)) := by
        rw [hMr]; exact rpow_root_shift Z _ _ hZ1 hNr0
      have hres : ∀ z, (keep'' z ∧ R1.rootOf z = r) →
          (R1.radRow st.character fixedBadMask z hm hmLam hm2).residue ≠ 1 := by
        intro z hz
        have hz0 := hnz'' z hz.1
        have hkz := hz.1
        rw [hk] at hkz
        have hex0 := st.nonexceptional z hkz.1.1
        rw [hpunc, CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff st.character
          st.fixedModulus fixedBadMask (idealGenerator 1) 1 z hm (idealGenerator_ne_zero 1 one_ne_zero)
          one_ne_zero hz0 hmLam hm2] at hex0
        exact R1.radRow_nonprincipal st.character st.fixedModulus fixedBadMask z hm hmLam hm2 hz0 hex0
      have hmod : ∀ z, (keep'' z ∧ R1.rootOf z = r) →
          ((R1.radRow st.character fixedBadMask z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Cscale * Z^Mr := by
        intro z hz
        obtain ⟨u', hu'⟩ := R1.rowMap_rootOf z (hnz'' z hz.1)
        rw [hz.2] at hu'
        have hkz := hz.1
        rw [hk] at hkz
        have hzN : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ * st.radial.scale := by
          rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]; exact hkz.2
        have hzg : z = u'.val * g^6 := by rw [hu', hg]; rfl
        subst hzg
        have hcond := R1.radRow_modulus_root st.character fixedBadMask u'.val g hm hmLam hm2
          u'.property.1 hg0
        have hspan : ((Ideal.span {u'.val * g^6}).absNorm : ℝ) =
            ((Ideal.span {u'.val}).absNorm : ℝ) * ((Ideal.span {g}).absNorm : ℝ)^6 := by
          rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, map_mul, map_pow]
          push_cast; ring
        have hgN : ((Ideal.span {g}).absNorm : ℝ) = R1.rootNorm r := by
          rw [hg]; exact R1.rootNorm_generator r
        rw [hspan, hgN] at hzN
        rw [hgN] at hcond
        have h5 : R1.rootNorm r ^ 6 * R1.rootNorm r ^ (-(5:ℝ)) = R1.rootNorm r := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hNr0]; norm_num
        have hNu : ((Ideal.span {u'.val}).absNorm : ℝ) * R1.rootNorm r ≤
            bΦ * st.radial.scale * R1.rootNorm r ^ (-(5:ℝ)) := by
          calc ((Ideal.span {u'.val}).absNorm : ℝ) * R1.rootNorm r
              = ((Ideal.span {u'.val}).absNorm : ℝ) * R1.rootNorm r ^ 6 * R1.rootNorm r ^ (-(5:ℝ)) := by
                rw [mul_assoc, h5]
            _ ≤ bΦ * st.radial.scale * R1.rootNorm r ^ (-(5:ℝ)) :=
                mul_le_mul_of_nonneg_right hzN (Real.rpow_nonneg hNr0.le _)
        have hcη0 : (0:ℝ) ≤ cη := le_trans (Nat.cast_nonneg _) hηmod
        have hcast : ((st.character.modulus.absNorm * (Ideal.span {fixedBadMask}).absNorm *
            (Ideal.span {(72 : O)}).absNorm : ℕ) : ℝ) ≤
            cη * ((Ideal.span {fixedBadMask}).absNorm : ℝ) * ((Ideal.span {(72:O)}).absNorm : ℝ) := by
          push_cast
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hηmod (Nat.cast_nonneg _)
        calc ((R1.radRow st.character fixedBadMask (u'.val * g^6) hm hmLam hm2).modulus.absNorm : ℝ)
            ≤ ((st.character.modulus.absNorm * (Ideal.span {fixedBadMask}).absNorm *
                (Ideal.span {(72 : O)}).absNorm : ℕ) : ℝ) *
              (((Ideal.span {u'.val}).absNorm : ℝ) * R1.rootNorm r) := hcond
          _ ≤ (cη * ((Ideal.span {fixedBadMask}).absNorm : ℝ) * ((Ideal.span {(72:O)}).absNorm : ℝ)) *
              (bΦ * st.radial.scale * R1.rootNorm r ^ (-(5:ℝ))) :=
              mul_le_mul hcast hNu (by positivity) (by positivity)
          _ = Cscale * Z^Mr := by rw [hCscale, hZMr, ← hU]; ring
      have hcap : ∀ z, (keep'' z ∧ R1.rootOf z = r) →
          ((R1.radRow st.character fixedBadMask z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Rcap := by
        intro z hz
        refine (hmod z hz).trans ?_
        rw [hRcap]
        refine le_trans ?_ (le_max_right _ _)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1.le hMrM) hCs.le
      obtain ⟨Xe, hXe⟩ : ∃ x : ℝ, x = max 1 (Z^(max 0 (Mr - Real.logb Z X₁ + u))) *
          (max 1 (9/4 * X₂) * ∏ i, Bs i) := ⟨_, rfl⟩
      have ha : max 0 (Mr - Real.logb Z X₁ + u) ≤ Mcap + 1 :=
        max_le (by linarith only [hMcap0]) (by linarith only [hMrM, hMc, hlogX, hu1])
      have hB0 : 0 ≤ max 1 (9/4 * X₂) * ∏ i : T, Bs i := by
        rw [hprodB]; have := le_max_left (1:ℝ) (9/4*X₂); positivity
      have hXeR : Xe ≤ Z^(Mcap + 1) * (cR * Z^(length Z X₂ + ∑ i ∈ T, w i)) := by
        rw [hXe]
        apply mul_le_mul _ hRrB hB0 (Real.rpow_nonneg hZ0.le _)
        exact max_le (Real.one_le_rpow hZ1.le (by linarith only [hMcap0])) (Real.rpow_le_rpow_of_exponent_le hZ1.le ha)
      have hXemax : Xe ≤ Z^auxCap := by
        refine hXeR.trans ?_
        have hc : cR ≤ Z := by
          calc cR ≤ (9/4) * 2^(Fintype.card α) := hcRle
            _ ≤ (9/4)^2 * 2^(Fintype.card α) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
            _ ≤ Z := hZbig
        have he : length Z X₂ + ∑ i ∈ T, w i ≤ Mcap + 5 := by linarith only [hl₂, hsT]
        calc Z^(Mcap + 1) * (cR * Z^(length Z X₂ + ∑ i ∈ T, w i))
            ≤ Z^(Mcap + 1) * (Z * Z^(Mcap + 5)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ0.le _)
              exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hZ1.le he) (Real.rpow_nonneg hZ0.le _)
                hZ0.le
          _ = Z^(2*Mcap + 7) := by
              rw [show 2*Mcap + 7 = (Mcap + 1) + (1 + (Mcap + 5)) by ring, Real.rpow_add hZ0 (Mcap + 1),
                Real.rpow_add hZ0 1, Real.rpow_one]
          _ ≤ Z^auxCap := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hauxCap, hMcap0])
      have hXe1 : 1 ≤ Xe := by
        rw [hXe]
        have h3 : 1 ≤ ∏ i : T, Bs i := by
          rw [hprodB]
          exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
            (Real.one_le_rpow hZ1.le hs0)
        exact one_le_mul_of_one_le_of_one_le (le_max_left _ _)
          (one_le_mul_of_one_le_of_one_le (le_max_left _ _) h3)
      have hΞb : Ce * Rcap^(u/(Mcap+1)) * (1 + 2*(max 0 (Mr - Real.logb Z X₁ + u) * Real.log Z)) +
          De * Rcap^(2*(u/(Mcap+1))) ≤ Ξ := by
        rw [hΞ]
        have hR0 : 0 ≤ Ce * Rcap^(u/(Mcap+1)) := mul_nonneg hCe.le (Real.rpow_nonneg (zero_le_one.trans hRcap1) _)
        have h1 : max 0 (Mr - Real.logb Z X₁ + u) * Real.log Z ≤ (Mcap+1) * Real.log Z :=
          mul_le_mul_of_nonneg_right ha hlogZ
        have h2 : 1 + 2*(max 0 (Mr - Real.logb Z X₁ + u) * Real.log Z) ≤ 1 + 2*((Mcap+1) * Real.log Z) := by
          linarith only [h1]
        exact add_le_add (mul_le_mul_of_nonneg_left h2 hR0) le_rfl
      have hML : Mr ≤ Mcap + Real.logb Z X₁ := by linarith only [hMrM, hMc, hlogX]
      have href := R1.root_bound_reflected n Se Ce De La (u/(Mcap+1)) Cscale u Mcap Z hrefl hZ1 hCe hDe
        hLa (cores.image Subtype.val) Y K Kn (Z^auxCap) Xe hY0 hK0 hK1 hnorm εd hεd st.character
        fixedBadMask g hm hmLam hm2 (fun z => keep'' z ∧ R1.rootOf z = r) st.radial.profile
        st.radial.scale st.radial.nonneg hUpos hcover hnzc (p.profile 0) (p.profile 1) (p.support 0)
        (p.support 1) c₁ c₂ Csc hSl hsc (fun i : T => primePool rayM H 2 (Z^(w i))) β
        (fun i : T => Z^(w i)) t Bs ms hB hms hres X₁ X₂ hX₁ hX₂ Mr Rcap hML hmod hRcap1 hcap
        (le_of_eq hXe.symm) hXemax Λ (hΛk Xe hXe1 hXemax _ le_rfl) (hΛk Xe hXe1 hXemax _ (by omega))
        Ξ hΞb
      have hfe : CenteredMomentOriginalRadialComparison.radialEnergy F
          (fun z => keep'' z ∧ R1.rootOf z = r) st.radial.profile st.radial.scale ≤ A * (Xe + Y) := by
        rw [hF]
        refine href.trans ?_
        rw [hA]
        exact weaken_lead _ _ _ _ _ _ _ (by positivity) hΓ2 (sq_nonneg _) (sq_nonneg _) hms0
          (by linarith only [hXe1, hY0])
      have hXeb : Xe ≤ cR * Z^(length Z X₂ + ∑ i ∈ T, w i) *
          max 1 (Z^(st.rowWidth - length Z X₁ + u) * R1.rootNorm r ^ (-(5:ℝ))) := by
        rw [hXe]
        have hm1 := max_one_rpow_max Z (Mr - Real.logb Z X₁ + u) hZ1
        have hshift : Z^(Mr - Real.logb Z X₁ + u) =
            Z^(st.rowWidth - length Z X₁ + u) * R1.rootNorm r ^ (-(5:ℝ)) := by
          rw [hℓ₁eq, hMr, show st.rowWidth - 5 * Real.logb Z (R1.rootNorm r) - Real.logb Z X₁ + u =
            (st.rowWidth - Real.logb Z X₁ + u) - 5 * Real.logb Z (R1.rootNorm r) by ring]
          exact rpow_root_shift Z _ _ hZ1 hNr0
        rw [hshift] at hm1
        calc max 1 (Z^(max 0 (Mr - Real.logb Z X₁ + u))) * (max 1 (9/4 * X₂) * ∏ i : T, Bs i)
            ≤ max 1 (Z^(st.rowWidth - length Z X₁ + u) * R1.rootNorm r ^ (-(5:ℝ))) *
              (cR * Z^(length Z X₂ + ∑ i ∈ T, w i)) :=
              mul_le_mul hm1 hRrB hB0 (zero_le_one.trans (le_max_left _ _))
          _ = _ := by ring
      have hX0 : 0 ≤ Z^(Mmin/20) + (bΦ * Z^st.rowWidth) * R1.rootNorm r ^ (-(6:ℝ)) +
          min (9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i))
            (cR * Z^(length Z X₂ + ∑ i ∈ T, w i) *
              max 1 (Z^(st.rowWidth - length Z X₁ + u) * R1.rootNorm r ^ (-(5:ℝ)))) := by
        have : 0 ≤ min (9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i))
            (cR * Z^(length Z X₂ + ∑ i ∈ T, w i) *
              max 1 (Z^(st.rowWidth - length Z X₁ + u) * R1.rootNorm r ^ (-(5:ℝ)))) :=
          le_min (by positivity) (mul_nonneg (by positivity) (zero_le_one.trans (le_max_left _ _)))
        positivity
      exact class_combine A Y Xd Xe _ _ _ _ _ _ _ hA0 hYb hXdD hXeb hX0 hfd hfe
    · -- the long plain length is below one: the direct bound alone
      rw [not_le] at hX₁1
      have hℓ₁0' : length Z X₁ = 0 := by
        unfold length; rw [max_eq_left hX₁1.le, Real.logb_one]
      have hDdRr : 9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i) ≤
          (9/4) * (cR * Z^(length Z X₂ + ∑ i ∈ T, w i)) := by
        rw [hℓ₁0', zero_add]; ring_nf; exact le_refl _
      exact class_combine_direct A Y Xd _ _ _ _ _ _ _ hA0 hYb hXdD (by positivity) (by positivity) hDdRr
        hY0 hfd
  ------------------------------------------------------------------ the sum over roots
  have hη' : 0 < u/(Mcap+1) := by positivity
  have hη'4 : u/(Mcap+1) ≤ 4 := by
    exact (div_le_self hu0.le (by linarith only [hMcap0])).trans (by linarith only [hu1])
  have hR6 : ∀ r ∈ R, R1.rootNorm r ^ (6:ℝ) ≤ bΦ * Z^st.rowWidth := by
    intro r hr
    rw [hR] at hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter, hPk] at hz
    obtain ⟨_, hkz, _⟩ := hz
    have hz0 := hnz'' z hkz
    rw [hk] at hkz
    obtain ⟨u', hu'⟩ := R1.rowMap_rootOf z hz0
    have hzN : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ * Z^st.rowWidth := by
      rw [← hU, ← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]; exact hkz.2
    have hN : ((Ideal.span {HeckeInverseAmplification.rowMap (u', R1.rootOf z)}).absNorm : ℝ) =
        ((Ideal.span {u'.val}).absNorm : ℝ) * ((R1.rootOf z).val.absNorm : ℝ)^6 := R1.absNorm_rowMap _
    have hzN' : ((Ideal.span {u'.val}).absNorm : ℝ) * ((R1.rootOf z).val.absNorm : ℝ)^6 ≤
        bΦ * Z^st.rowWidth := by
      rw [← hN, ← hu']; exact hzN
    have hu1 : (1:ℝ) ≤ ((Ideal.span {u'.val}).absNorm : ℝ) := ProbeHighRowFamily.rowNorm_ge_one u'
    have h6 : R1.rootNorm (R1.rootOf z) ^ (6:ℝ) = ((R1.rootOf z).val.absNorm : ℝ)^6 := by
      unfold R1.rootNorm; rw [← Real.rpow_natCast]; norm_num
    rw [h6]
    have h60 : 0 ≤ ((R1.rootOf z).val.absNorm : ℝ)^6 := by positivity
    calc ((R1.rootOf z).val.absNorm : ℝ)^6 = 1 * ((R1.rootOf z).val.absNorm : ℝ)^6 := (one_mul _).symm
      _ ≤ ((Ideal.span {u'.val}).absNorm : ℝ) * ((R1.rootOf z).val.absNorm : ℝ)^6 :=
          mul_le_mul_of_nonneg_right hu1 h60
      _ ≤ bΦ * Z^st.rowWidth := hzN'
  have hS1 := hsum ((9/4) * A) (9/4 * cR * Z^(length Z X₁ + length Z X₂ + ∑ i ∈ T, w i))
    (cR * Z^(length Z X₂ + ∑ i ∈ T, w i)) (Z^(st.rowWidth - length Z X₁ + u)) (Z^(Mmin/20))
    (bΦ * Z^st.rowWidth) (u/(Mcap+1)) (by positivity) (by positivity) (by positivity)
    (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hZ0.le _) (by positivity) hη' hη'4 R _ hR6 hroot
  have hbr := R1.bracket_bound Z st.rowWidth Mmin Mcap (length Z X₁) (length Z X₂) (∑ i ∈ T, w i) u bΦ cR
    (R1.rootZeta (1 + u/(Mcap+1))) C₆ hZ1 hMmin hMlow hMc hℓ₂0 hℓ hs0 hu0 (by linarith only [hu1])
    (by linarith only [hbΦ])
    hcR0 (R1.rootZeta_nonneg _) hC₆.le
  ------------------------------------------------------------------ the class constant
  have hΛb : Λ ≤ (max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd))^(2 + Fintype.card α) * Z^u := by
    rw [hΛ, hβ₀]
    exact lambda_bound Z auxCap εd u _ (Fintype.card T) (Fintype.card α) hZ1
      (by linarith only [hauxCap, hMcap0]) hεd.le hcardT
      hεdDef
  have hΞb : Ξ ≤ (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) * Z^(2*u) := by
    rw [hΞ, hRcap]
    exact xi_bound Z st.rowWidth Mcap u Cscale Ce De hZ1 hM0 hMc hu0 (by linarith only [hu1]) hCe.le hDe.le
  have hΓb : Γ ≤ ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
      (128 * La^2 * (128*(9/4))) * Csc^2) * Z^(2*u) * (1+|t|+height)^(2*n) := by
    rw [hΓ]
    have hZ2u : 1 ≤ Z^(2*u) := Real.one_le_rpow hZ1.le (by linarith only [hu0])
    have hT2 : (1+‖t‖)^(2*n) ≤ (1+|t|+height)^(2*n) := by
      apply pow_le_pow_left₀ (by positivity); rw [Real.norm_eq_abs]; linarith only [hh]
    have hK : 0 ≤ 128 * La^2 * (128*(9/4)) * Csc^2 := by positivity
    have h1 : (128*(9/4):ℝ)^2 + Ξ * (128 * La^2 * (128*(9/4))) * Csc^2 ≤
        ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
          (128 * La^2 * (128*(9/4))) * Csc^2) * Z^(2*u) := by
      have h2 : Ξ * (128 * La^2 * (128*(9/4))) * Csc^2 ≤
          ((Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) * Z^(2*u)) *
            (128 * La^2 * (128*(9/4))) * Csc^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΞb (by positivity)) (by positivity)
      have h3 : (128*(9/4):ℝ)^2 ≤ (128*(9/4))^2 * Z^(2*u) := le_mul_of_one_le_right (by positivity) hZ2u
      calc (128*(9/4):ℝ)^2 + Ξ * (128 * La^2 * (128*(9/4))) * Csc^2
          ≤ (128*(9/4))^2 * Z^(2*u) + ((Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) +
              De * (max 1 Cscale)^2) * Z^(2*u)) * (128 * La^2 * (128*(9/4))) * Csc^2 := add_le_add h3 h2
        _ = _ := by ring
    exact mul_le_mul h1 hT2 (by positivity) (by positivity)
  have hctl : c₁ * c₂ = p.control S := by rw [hc₁, hc₂]; rfl
  have hmsb : ∏ i : T, ms i ≤ (max 1 (256 * LW^2))^(Fintype.card α) := by
    rw [hprodm]
    exact (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hcardT)
  have hAb := A_bound (QuadraticInitialBound.diagonalControl st.radial.profile) Kn Knorm (Z^u) Λ
    ((max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd))^(2 + Fintype.card α)) Γ
    ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
      (128 * La^2 * (128*(9/4))) * Csc^2) (Z^(2*u)) ((1+|t|+height)^(2*n)) c₁ c₂ (p.control S)
    (∏ i : T, ms i) ((max 1 (256 * LW^2))^(Fintype.card α)) hdiag0 hKn hKnorm.le
    (Real.rpow_nonneg hZ0.le _) hΛb hΛ0 (by positivity) hΓb hΓ0 (by positivity)
    (Real.rpow_nonneg hZ0.le _) (by positivity) hctl hmsb hms0
  rw [← hA] at hAb
  have hZ4 : Z^u * Z^u * Z^(2*u) = Z^(4*u) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; ring_nf
  rw [hZ4] at hAb
  have hCB : R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + cR) + C₆ * bΦ +
      R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * cR ≤
      R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + (9/4) * 2^(Fintype.card α)) + C₆ * bΦ +
        R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * ((9/4) * 2^(Fintype.card α)) := by
    have hζ0 := R1.rootZeta_nonneg (1 + u/(Mcap+1))
    have h1 := mul_le_mul_of_nonneg_left hcRle (mul_nonneg hζ0 hbΦ0.le)
    have h2 := mul_le_mul_of_nonneg_left hcRle (mul_nonneg hζ0 (by norm_num : (0:ℝ) ≤ 9/4))
    calc R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + cR) + C₆ * bΦ + R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * cR
        = R1.rootZeta (1 + u/(Mcap+1)) * bΦ + R1.rootZeta (1 + u/(Mcap+1)) * bΦ * cR + C₆ * bΦ +
            R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * cR := by ring
      _ ≤ R1.rootZeta (1 + u/(Mcap+1)) * bΦ + R1.rootZeta (1 + u/(Mcap+1)) * bΦ * ((9/4) * 2^(Fintype.card α)) +
            C₆ * bΦ + R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * ((9/4) * 2^(Fintype.card α)) := by
          linarith only [h1, h2]
      _ = _ := by ring
  have hCBZ0 : 0 ≤ R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + cR) + C₆ * bΦ +
      R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * cR := by
    have := R1.rootZeta_nonneg (1 + u/(Mcap+1)); positivity
  have hrest : 0 ≤ (2 * Knorm * (max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd))^(2 + Fintype.card α) *
      ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
        (128 * La^2 * (128*(9/4))) * Csc^2) * (max 1 (256 * LW^2))^(Fintype.card α)) *
      QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 * (1+|t|+height)^(2*n) := by
    have := le_max_left (1:ℝ) (Qrh.JointDetector.idealDivisorConstant εd hεd)
    positivity
  exact final_combine _ A _ _ _ _ _ u ε _ _ _ Z hZ1 hu0.le (by linarith only [huε, hu0]) hS1 hbr hA0 hAb hCB hCBZ0 hrest

end
end QRH.ArviSelectedLeaf
