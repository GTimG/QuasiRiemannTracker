/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
One uniform bound for every native leaf of the reference rectangle: one ordinary
length is short (`≤ Z^ℓ`); if the other has `log_Z`-length `≤ 1/2` the leaf is paid directly by
the parent, otherwise the long factor is naturally reflected (`reflected_leaf`). The bound is
`Ktot·(ctl W₁·ctl W₂)²·(1+|t|+V)^J·Z^(1+ε+4ε_R)`. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Reflect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic ConcreteTraceCRT
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalRowSource
open QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The per-`Z` content of `natural_reference_reflection_homogeneous` (profiles on
`[1/4, 9/4]`, slot types in `Type`). -/
def ReflectionAt (bΦ epsilon xi saving L : ℝ) (J n : ℕ) (S : Finset (ℕ×ℕ)) (C D Z : ℝ) : Prop :=
  ∀ (Bmask : ℝ) (s : NaturalState Z Bmask bΦ) (Wlong Wshort : 𝓢(ℝ,ℂ)),
    Function.support (Wlong:ℝ→ℂ) ⊆ Icc (1/4) (9/4) →
    Function.support (Wshort:ℝ→ℂ) ⊆ Icc (1/4) (9/4) →
    ∀ (α : Type) (F : Finset α) (pool : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
      (t along bshort E : ℝ),
    s.width ≤ L+along → 0 ≤ E →
    (∀ v : ℝ, ∀ j k : Fin 2, ∀ x ∈ Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
      radialEnergy (fun z => polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ => (annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) *
        polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Z^bshort) 0 t *
        ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤ E*(1+‖v‖)^(2*J)) →
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        radialEnergy (fun z => polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale

theorem reflection_eventually (bΦ epsilon xi : ℝ) (hbΦ : 0 < bΦ) (heps : 0 < epsilon)
    (hxi : 0 < xi) (J : ℕ) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ReflectionAt bΦ epsilon xi 1 2 J n S C D Z := by
  obtain ⟨n, S, C, D, hC, hD, h⟩ :=
    CenteredMomentEnergyReferenceHomogeneous.natural_reference_reflection_homogeneous
      (1/4) (9/4) bΦ epsilon xi 1 2 (by norm_num) (by norm_num) hbΦ heps hxi 2 J le_rfl
  exact ⟨n, S, C, D, hC, hD, h.mono fun Z hZ => ⟨hZ.1,
    fun Bmask s Wl Ws hl hs α F pool β P t along bshort E =>
      hZ.2 Bmask s Wl Ws hl hs α F pool β P t along bshort E⟩⟩

theorem conductor_max_le (c Z δ : ℝ) (hc : 0 ≤ c) (hZ : 1 ≤ Z) (hcZ : c ≤ Z) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) : max 1 (c*Z^(1+δ)) ≤ Z^(3:ℝ) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  refine max_le (Real.one_le_rpow hZ (by norm_num)) ?_
  calc c*Z^(1+δ) ≤ Z*Z^(1+δ) := mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)
    _ = Z^(1+(1+δ)) := by rw [Real.rpow_add hZ0 (1:ℝ) (1+δ), Real.rpow_one]
    _ ≤ Z^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem conductor_pow_le (c Z δ e : ℝ) (hc : 0 ≤ c) (hZ : 1 ≤ Z) (hcZ : c ≤ Z) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (he : 0 ≤ e) : (max 1 (c*Z^(1+δ)))^e ≤ Z^(3*e) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  calc (max 1 (c*Z^(1+δ)))^e ≤ (Z^(3:ℝ))^e :=
        Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) (conductor_max_le c Z δ hc hZ hcZ hδ hδ1) he
    _ = Z^(3*e) := by rw [← Real.rpow_mul hZ0.le]

/-- The two-profile control of independent phase profiles, through a finite seminorm set. -/
theorem independent_control_le (SP TD control : Finset (ℕ×ℕ)) (nD : ℕ) (CD : ℝ) (hCD : 0 ≤ CD)
    (hnp : ∀ (W : 𝓢(ℝ,ℂ)) (hs : Function.support (W:ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (t : ℝ),
      SP.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤) t) ≤
        CD*TD.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^nD)
    (hTD : TD ⊆ control)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (t h : ℝ) (hth : 1+‖t‖ ≤ h) :
    ((independentProfiles (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t t).control SP)^2 ≤
      CD^4*(sourceControl control W₁*sourceControl control W₂)^2*h^(4*nD) := by
  have e : (independentProfiles (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t t).control SP =
      SP.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W₁ (1/4) (9/4) (by norm_num) hs₁
        (W₁.smooth ⊤) t) *
      SP.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W₂ (1/4) (9/4) (by norm_num) hs₂
        (W₂.smooth ⊤) t) := by
    simp only [Profiles.control, sourceControl, independentProfiles, ite_true,
      show (1:Fin 2) ≠ 0 by decide, ite_false]
  have hmono (W : 𝓢(ℝ,ℂ)) : TD.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ sourceControl control W :=
    Seminorm.le_def.mp (Finset.sup_mono hTD) W
  have h0 : 0 ≤ 1+‖t‖ := by positivity
  have hp : (1+‖t‖)^nD ≤ h^nD := pow_le_pow_left₀ h0 hth nD
  have hq : 0 ≤ (1+‖t‖)^nD := by positivity
  have b1 := (hnp W₁ hs₁ t).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hmono W₁) hCD) hp hq
    (mul_nonneg hCD (sourceControl_nonneg _ _)))
  have b2 := (hnp W₂ hs₂ t).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hmono W₂) hCD) hp hq
    (mul_nonneg hCD (sourceControl_nonneg _ _)))
  have hprod := mul_le_mul b1 b2 (apply_nonneg _ _) (by
    have := sourceControl_nonneg control W₁; have := h0.trans hth; positivity)
  rw [e]
  have hsq := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hprod 2
  refine hsq.trans (le_of_eq ?_)
  rw [show 4*nD = nD*4 by ring, pow_mul]
  ring

end
end Qrh.MarkedAnchor.Ordinary.Reference
