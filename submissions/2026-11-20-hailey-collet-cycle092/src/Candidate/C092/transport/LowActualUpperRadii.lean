/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The genuine low-response step uniformly above H. -/
import Candidate.C092.transport.LowActualFiniteCover

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.WholeSlot QRH.Cycle090 QRH.SourceCertificate
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open OAI.SevenEighths.Cycle61Moment CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

/-- A preceding genuine source closes the original positive low-response
energy at H. The original mesh precedes every finite mark and label; its
buffer precedes the slot supplier's constant; all energy constants precede
U, whole-slot widths, phases, ordinary tests and lengths. -/
theorem low_step_above_H {n y e Vmax : ℝ}
    (hmax : (H : ℝ) ≤ Vmax)
    (hwidth : 0 < sourceWidth (n/(H : ℝ)) (y/(H : ℝ)))
    (hprev : OpenWidth (n/(H : ℝ)) (y/(H : ℝ)))
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ)) :
    ∃ mesh : ℝ, 0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ, 0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∀ Cslot : ℝ, 0 ≤ Cslot →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ, (H : ℝ) ≤ V → V ≤ Vmax →
    ∀ (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, w j ≤ mesh) →
      (∀ j, (33/50 : ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50 : ℝ)) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) → ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ →
      Box (n/(H : ℝ)) (y/(H : ℝ)) 0
        (length (U^V) X₁) (length (U^V) X₂) 0 →
      (∑ j, w j) ≤ sourceWidth n y-(u : ℝ) →
      energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
        (fun j => U^(w j)) X₁ X₂
        (fun z => initialKeep η (internalQ Q η₀) z ∧
          LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
            (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
            (fun j => U^(w j)) z) Φ (U^V) ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4) := by
  obtain ⟨decrement,rounding,hd,hdw,hr,hfee⟩ := p3_early_rounding hwidth
  let l := sourceWidth (n/(H : ℝ)) (y/(H : ℝ))-decrement
  have hl : 0 < l := sub_pos.mpr hdw
  have hlw : l < sourceWidth (n/(H : ℝ)) (y/(H : ℝ)) := sub_lt_self _ hd
  have hprevious := hprev l hl.le hlw
  let εsrc : ℝ := (rho : ℝ)/(16*Vmax)
  have hmaxpos : 0 < Vmax := H_real_bounds.1.trans_le hmax
  have hεsrc : 0 < εsrc := by
    have hrho : (0 : ℝ) < (rho : ℝ) := by norm_num [rho]
    exact div_pos hrho (mul_pos (by norm_num) hmaxpos)
  have hεfee : Vmax*εsrc = (rho : ℝ)/16 := by
    dsimp [εsrc]; field_simp
  obtain ⟨sourceMesh,hsm,hsource⟩ := uniformBox_radius hprevious hεsrc H_real_bounds.1
  let mesh := min rounding ((H : ℝ)*sourceMesh)
  have hm : 0 < mesh := lt_min hr (mul_pos H_real_bounds.1 hsm)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  let buffer : ℝ := (rho : ℝ)/(16*(1+(Fintype.card Slot : ℝ)))
  have hb : 0 < buffer := by
    have hrho : (0 : ℝ) < (rho : ℝ) := by norm_num [rho]
    dsimp [buffer]; positivity
  have hbfee : buffer*(Fintype.card Slot : ℝ) ≤ (rho : ℝ)/16 := by
    have hEq : buffer*(16*(1+(Fintype.card Slot : ℝ))) = (rho : ℝ) := by
      dsimp [buffer]; field_simp
    nlinarith
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72 Cslot hCslot
  obtain ⟨degree,controls,Csrc,hCsrc,hsourceU⟩ := hsource Slot rayM Hr hHr W hW hWs bΦ hbΦ
    η η₀ Q hQray hQ0 hQt hQ72
  let C := (max 1 Cslot)^(Fintype.card Slot)*Csrc
  have hC : 0 < C := mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hCsrc
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsourceU,eventually_ge_atTop (1 : ℝ)] with U hsourceU hU
  intro V hVH hVmax θ w σ v t height
  have hV : 0 < V := H_real_bounds.1.trans_le hVH
  intro hw hwm hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox hwidthU
  obtain ⟨F,hF,hdel,hex,hboxes⟩ := selection_with_source_boxes w mesh V l hw hwm hm.le hV.le hl.le
  have hcard : (Finset.univ\F).card ≤ Fintype.card Slot := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  have herror : buffer*((Finset.univ\F).card : ℝ)+V*εsrc ≤ (rho : ℝ)/4 := by
    have hc : ((Finset.univ\F).card : ℝ) ≤ (Fintype.card Slot : ℝ) := by exact_mod_cast hcard
    have h := mul_le_mul_of_nonneg_left hc hb.le
    have hvfee := mul_le_mul_of_nonneg_right hVmax hεsrc.le
    rw [hεfee] at hvfee
    linarith [show (0 : ℝ) < (rho : ℝ) by norm_num [rho]]
  have hround : 2*(responseUpper : ℝ)*((H : ℝ)*decrement+mesh) ≤ (rho : ℝ) := by
    have hmround : mesh ≤ rounding := min_le_left _ _
    have hrpos : (0 : ℝ) ≤ 2*(responseUpper : ℝ) := by norm_num [responseUpper]
    have hadd : (H : ℝ)*decrement+mesh ≤ (H : ℝ)*decrement+rounding := by linarith
    exact (mul_le_mul_of_nonneg_left hadd hrpos).trans hfee
  have hpriceH := p3_paid_with_rounding (n := n) he0 he1 hd.le hm.le hround hp
  have hcap : (H : ℝ)*l ≤ V*l := mul_le_mul_of_nonneg_right hVH hl.le
  have hprice : e*max 0 (sourceWidth n y-(u : ℝ)-V*l+mesh) <
      (u : ℝ)-(rho : ℝ)/2 :=
    (mul_le_mul_of_nonneg_left (max_le_max_left 0 (by linarith)) he0).trans_lt hpriceH
  have hwm' (j : Slot) : w j/V ≤ sourceMesh :=
    mesh_rescale H_real_bounds.1 hVH hsm.le (min_le_right _ _) (hwm j)
  have hE := actual_low_energy (e := e) rayM Hr hHr (hsourceU V hVH) F θ w σ v t height mesh
    hw hwm' hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hU hV hCslot hCsrc.le he0
    (hboxes _ _ _ _ hbox) hwidthU hdel hprice herror
  have hc : Cslot^(Finset.univ\F).card*Csrc ≤ C := by
    dsimp [C]
    apply mul_le_mul_of_nonneg_right _ hCsrc.le
    calc
      _ ≤ (max 1 Cslot)^(Finset.univ\F).card := by gcongr; exact le_max_right _ _
      _ ≤ (max 1 Cslot)^(Fintype.card Slot) := by gcongr; exact le_max_left _ _
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hheight : 0 ≤ (1+|t|+height)^degree := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
      (1+|t|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4) by positivity)
  calc
    _ ≤ _ := hE
    _ ≤ _ := by nlinarith [hmul]

end
end QRH.Cycle092.LowActual
