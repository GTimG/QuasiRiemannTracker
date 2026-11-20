/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Large measured-response branch
of P.1 on the original fixed-cofactor core. -/
import Candidate.C092.transport.MeasuredPair
import Candidate.C092.transport.SixthCore
import Candidate.C092.transport.NativeStrip
namespace QRH.Cycle092.MeasuredBall
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion Qrh.JointDetector WholeWordAmplification
open QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O
local instance c092LocalInst_Candidate_C092_transport_MeasuredBall_4a5775a17c5a0635_001 (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

open QRH.Cycle090 CenteredMomentEnergyBands LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092.MeasuredPair QRH.Cycle092.SixthCore

/-- The ordered P.1 rectangle gives the exact support cap in either orientation. -/
theorem support_cap {Z P Q s n y : ℝ} (hZ : 1 < Z) (hP : 0 < P) (hQ : 0 < Q)
    (hy : sourceY0 ≤ y) (hy' : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (hbox : NativeStrip.Box n y (sourceWidth n y) (length Z P) (length Z Q) s) :
    P * Q * Z^s ≤ Z^(9179599/10000000:ℝ) := by
  obtain ⟨_,_,hp,_,hs⟩ := hbox
  have hg := Source.sourceGain_quarter_secant hy hy' le_rfl
  rw [source_native_value] at hg
  unfold sourceWidth at hs; norm_num [sourceY,sourceRatio] at hg hn hy'
  have hex : length Z P + length Z Q + s ≤ 9179599/10000000 := by rcases hp with ⟨_,_⟩ | ⟨_,_⟩ <;> linarith
  have h0 := zero_lt_one.trans hZ
  have hlen (X : ℝ) : X ≤ Z^length Z X := by
    rw [length,Real.rpow_logb h0 hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]; exact le_max_right _ _
  calc
    _ ≤ Z^length Z P * Z^length Z Q * Z^s := by gcongr <;> first | exact hlen _ | positivity
    _ = _ := by rw [←Real.rpow_add h0,←Real.rpow_add h0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hex

theorem fiber_mem {R : Finset NonzeroFrequency} {B : HeckeInverseAmplification.NonzeroIdeal} {u : FreeRow}
    (hu : u ∈ sixthFreeFiber R B) : sixthFrequencyEquiv (u,B) ∈ R := by
  obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨hp,hpB⟩ := Finset.mem_filter.mp hp
  exact (mem_sixthPairs R (u,B)).mp ((Prod.ext hpu hpB : p=(u,B)) ▸ hp)

theorem core_identity {Z : ℝ} (hZ : 1 < Z) (M : ℝ) (B : HeckeInverseAmplification.NonzeroIdeal) :
    Z^coreWidth Z M B = Z^M / (B.val.absNorm : ℝ)^(6:ℕ) := by
  have hN : 0 < (B.val.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have h0 := zero_lt_one.trans hZ
  rw [coreWidth,Real.rpow_sub h0,mul_comm (6:ℝ), Real.rpow_mul h0.le,Real.rpow_logb h0 hZ.ne' hN]
  norm_cast

/-- Summing the actual (possibly sparse) cofactor classes costs only a uniform constant. -/
theorem raw_sum : ∃ D : ℝ, 0 < D ∧ ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency → ℝ)
    (Z M e K : ℝ), 1 < Z → 0 ≤ K → (∀ B : HeckeInverseAmplification.NonzeroIdeal, (sixthFreeFiber R B).Nonempty →
      ∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u,B)) ≤ K*Z^(coreWidth Z M B + e)) →
    ∑ h ∈ R, f h ≤ K*D*Z^(M+e) := by
  let w : HeckeInverseAmplification.NonzeroIdeal → ℝ := fun B => (B.val.absNorm:ℝ)^(-6*(1:ℝ))
  have hw : Summable w := ideal_sixth_power_summable 1 (by norm_num)
  have hw0 (B : HeckeInverseAmplification.NonzeroIdeal) : 0 ≤ w B := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnon : 0 ≤ ∑' B, w B := tsum_nonneg hw0
  refine ⟨(∑' B, w B)+1, by linarith, ?_⟩
  intro R f Z M e K hZ hK hbound
  have h0 := zero_lt_one.trans hZ
  rw [raw_sixth_weighted_sum]; let roots := (sixthPairs R).image Prod.snd
  calc
    _ ≤ ∑ B ∈ roots, (K*Z^(M+e))*w B := by
      apply Finset.sum_le_sum; intro B hB
      refine (hbound B (cofactor_fiber_nonempty R B hB)).trans_eq ?_
      have hN : 0 < (B.val.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
      simp only [Real.rpow_add h0,core_identity hZ,w,mul_one,Real.rpow_neg hN.le,Real.rpow_ofNat,div_eq_mul_inv]; ring
    _ = (K*Z^(M+e))*∑ B ∈ roots, w B := (Finset.mul_sum ..).symm
    _ ≤ (K*Z^(M+e))*((∑' B,w B)+1) := by gcongr; linarith [hw.sum_le_tsum roots (fun B _ => hw0 B)]
    _ = _ := by ring

theorem ball (amax loss : ℝ) (ha : 1 ≤ amax) (hl : 0 < loss) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (W : ℝ → ℂ), Continuous W →
    Function.support W ⊆ Icc (1:ℝ) 2 → ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (bΦ : ℝ) (st : NaturalState Z 0 bΦ) (η₀ : Character) (T : Finset α)
    (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t mesh pay M n y : ℝ) (R : Finset NonzeroFrequency),
      0 ≤ mesh → mesh ≤ μ → (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) → (∀ k, σ k ∈ Icc (33/50:ℝ) (33/50)) →
      Z^(2*b) ≤ pay → M ≤ amax → (∀ h ∈ R, rawFrequencyNorm h ≤ Z^M ∧ 98/100 ≤ coreWidth Z M (sixthFrequencyEquiv.symm h).2 ∧ 5002/10000 < response rayM H hH st η₀ W T θ w σ v t pay h.val) →
    ∀ (η₁ η₂ : Character) (m A₁ A₂ : O), goodLambda ∣ m → (2:O) ∣ m →
    ∀ (W₁ W₂ : ℝ → ℂ) (t₁ t₂ P Q B₁ B₂ : ℝ), 0 < P → 0 < Q →
      Function.support W₁ ⊆ Iic (9/4:ℝ) → Function.support W₂ ⊆ Iic (9/4:ℝ) →
      (∀ I ∈ idealBall (9/4*P), ‖W₁ ((I.absNorm:ℝ)/P)‖ ≤ B₁) → (∀ I ∈ idealBall (9/4*Q), ‖W₂ ((I.absNorm:ℝ)/Q)‖ ≤ B₂) →
      sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y → NativeStrip.Box n y (sourceWidth n y) (length Z P) (length Z Q) (∑ i,w i) →
      (∑ h ∈ R, (‖original η₁ m A₁ h.val W₁ t₁ P‖^2 * ‖original η₂ m A₂ h.val W₂ t₂ Q‖^2)*
        RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t h.val) ≤ C*Z^(M-305/10000+loss)*(B₁^2*B₂^2) := by
  obtain ⟨μ,hμ,hop⟩ := MeasuredPair.energy amax loss ha hl
  obtain ⟨D,hD,hsum⟩ := raw_sum
  refine ⟨μ,hμ,?_⟩; intro α _ _ W hW hs b hb
  obtain ⟨C,hC,he⟩ := hop α W hW hs b hb
  refine ⟨C*D,mul_pos hC hD,?_⟩
  filter_upwards [he] with Z h; obtain ⟨hZ,hen⟩ := h
  refine ⟨hZ,?_⟩; intro rayM _ H hH bΦ st η₀ T θ w σ v t mesh pay M n y R hm hm' hw hwm hσ hp hM hrows η₁ η₂ m A₁ A₂ hm₁ hm₂ W₁ W₂ t₁ t₂ P Q B₁ B₂ hP hQ hs₁ hs₂ hW₁ hW₂ hy hy' hn hbox
  let f (h : NonzeroFrequency) : ℝ := (‖original η₁ m A₁ h.val W₁ t₁ P‖^2*‖original η₂ m A₂ h.val W₂ t₂ Q‖^2)*RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t h.val
  have hbnd := hsum R f Z M (-305/10000+loss) (C*(B₁^2*B₂^2)) hZ (by positivity) (by
    intro B hB
    let V := coreWidth Z M B
    obtain ⟨u,hu⟩ := hB
    have hV : 98/100 ≤ V := by simpa [V] using (hrows _ (fiber_mem hu)).2.1
    have hY : 1 ≤ Z^V := Real.one_le_rpow hZ.le (by linarith)
    have hYa := Real.rpow_le_rpow_of_exponent_le hZ.le ((coreWidth_le Z M hZ B).trans hM)
    have hrad (u : FreeRow) (hu : u ∈ sixthFreeFiber R B) : rowNorm u ≤ Z^V := by
      have hraw := (hrows _ (fiber_mem hu)).1; rw [raw_sixth_norm] at hraw
      rw [show Z^V = _ from core_identity hZ M B]; apply (le_div_iff₀ ?_).2 hraw
      exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)) _
    have hh := hen rayM H hH bΦ st η₀ T θ w σ v t mesh pay V (Z^V) B (sixthFreeFiber R B) hm hm' hw hwm hσ hp (fun u hu => (hrows _ (fiber_mem hu)).2.2) hV hY hYa le_rfl hrad η₁ η₂ m A₁ A₂ hm₁ hm₂ W₁ W₂ t₁ t₂ P Q B₁ B₂ hP hQ hs₁ hs₂ hW₁ hW₂ (support_cap hZ hP hQ hy hy' hn hbox)
    apply hh.trans_eq; dsimp only [V]; rw [show coreWidth Z M B - 305/10000 + loss = coreWidth Z M B + (-305/10000+loss) by ring]; ring)
  apply hbnd.trans_eq; rw [show M-305/10000+loss = M+(-305/10000+loss) by ring]; ring

#print axioms ball
end
end QRH.Cycle092.MeasuredBall
