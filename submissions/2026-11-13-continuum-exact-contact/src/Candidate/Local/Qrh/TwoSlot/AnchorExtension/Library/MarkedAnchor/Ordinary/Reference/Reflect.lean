/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Natural reflection of the long ordinary factor of a leaf: the reflected children
(dual annular pieces of length `≤ Z^(1+δ-along+ξ) ≤ Z^(1/2+δ+ξ)`, the short profile and the
canonical slots) lie in the parent face `G(.99, 49/20, .14)` and are paid by its initial energy;
the natural reflection (`natural_reference_reflection_homogeneous`, passed as its per-`Z`
instance) then bounds the leaf. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Leaf
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow

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
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceLowWindow
open QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem length_le_of_logb (Z X ℓ : ℝ) (hZ : 1 < Z) (hX : 0 < X) (hℓ : 0 ≤ ℓ)
    (h : Real.logb Z X ≤ ℓ) : length Z X ≤ ℓ := by
  unfold length
  rcases le_total X 1 with h1 | h1
  · rw [max_eq_left h1, Real.logb_one]; exact hℓ
  · rw [max_eq_right h1]; exact h

section
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Id) [NeZero M]
local instance instFiniteQuotReflect : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- **Reflected children are paid by the parent**: every dual window of the natural reflection
of a long factor of length `Z^along`, `along ≥ 1/2`, against a short factor `Z^bshort`,
`bshort ≤ lref`, at the initial state of width `1+δ`. -/
theorem child_bound (W : ℝ → ℂ) (η η₀ : Character) (Q₀ : Id) (hQ₀ : internalQ Q₀ η₀ = Q₀)
    (Ψ : 𝓢(ℝ,ℂ)) (bΨ : ℝ) (hΨs : Function.support (Ψ:ℝ → ℂ) ⊆ Iic bΨ) (hΨ : ∀ x, 0 ≤ (Ψ x).re)
    (meshP ε : ℝ) (dP : ℕ) (SP : Finset (ℕ×ℕ)) (CP Z δ : ℝ) (hCP : 0 ≤ CP)
    (hZ : 1 < Z) (hδ : 0 ≤ δ) (hη : (η.modulus.absNorm:ℝ) ≤ Z^δ)
    (hP : InitialAffineAt (α:=α) M H hH (globalFace Bref Lref cref) W 2 (1/4) (9/4) bΨ meshP
      (33/50) (33/50) 1 1 ε Z η η₀ Q₀ dP SP CP)
    (nC : ℕ) (TC : Finset (ℕ×ℕ)) (DC : ℝ)
    (hctl : ∀ (W' : 𝓢(ℝ,ℂ)) (hs : Function.support (W':ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (j k : Fin 2)
      (v t height : ℝ), 0 ≤ height →
      ((reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num) W' hs j k v t).control SP)^2*
        (1+|t|+height)^dP ≤
        DC*(sourceControl TC W')^2*(1+|t|+height)^(dP+2*nC)*(1+‖v‖)^(2*nC))
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ meshP) (hσ : ∀ i, σ i = 33/50)
    (hV : 0 ≤ V) (hfreq : ∀ i, |freq i| ≤ V)
    (Wshort : 𝓢(ℝ,ℂ)) (hsW : Function.support (Wshort:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (F : Finset α) (along bshort xi ℓ : ℝ) (hxi : 0 ≤ xi) (hlong : 1/2 ≤ along)
    (hb : bshort ≤ ℓ) (hℓ : 0 ≤ ℓ)
    (hgate : ℓ + (1/2 + δ + xi) + Lref*(∑ i ∈ F, w i) ≤ Bref) (hcap : ∑ i ∈ F, w i ≤ cref) :
    ∀ v : ℝ, ∀ j k : Fin 2,
      ∀ x ∈ Icc 0 (max 0 ((initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).width - along + xi)*
        Real.log Z),
      radialEnergy (fun z =>
          polynomial (naturalCharacter (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).character z) false
            (scaleTest (fun y:ℝ => (annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) *
          polynomial (naturalCharacter (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).character z) false
            (scaleTest Wshort k) (Z^bshort) 0 t *
          ∏ i ∈ F, naturalSlot
            (naturalCharacter (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).character z)
            (primePool M H 2 (Z^(w i)))
            (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
        (effectiveState (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη)).radial.keep
        (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).radial.profile
        (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).radial.scale ≤
      (CP*diagonalControl Ψ*DC*(sourceControl TC Wshort)^2*(1+|t|+V)^(dP+2*nC)*Z^(1+ε))*
        (1+‖v‖)^(2*nC) := by
  intro v j k x hx
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hwidth : (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).width = 1+δ := rfl
  have hwin := reflection_window_length Z _ x hZ (le_max_left _ _) hx
  have hl1 : length Z (Real.exp x) ≤ 1/2+δ+xi :=
    hwin.1.trans (max_le (by positivity) (by rw [hwidth]; linarith))
  have hl2 : length Z (Z^bshort) ≤ ℓ :=
    length_le_of_logb Z _ ℓ hZ (Real.rpow_pos_of_pos hZ0 _) hℓ
      (by rw [Real.logb_rpow hZ0 hZ.ne']; exact hb)
  have hsF : 0 ≤ ∑ i ∈ F, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hL : (0:ℝ) ≤ Lref := by norm_num [Lref]
  have hadm := (globalFace_admissible_iff (length_nonneg Z (Real.exp x) hZ)
    (length_nonneg Z (Z^bshort) hZ) hsF hL (B := Bref) (cap := cref) (M := 1)).mpr
    ⟨by rw [mul_one]; exact hcap, by rw [mul_one]; linarith⟩
  have h1 := reflected_child M H hH W η η₀ Q₀ hQ₀ Ψ bΨ hΨs hΨ meshP ε dP SP CP Z δ hZ hδ hη hP
    θ w σ freq t V hw hwm hσ hV hfreq Wshort hsW F j k v (Real.exp x) (Z^bshort)
    (Real.exp_pos x) (Real.rpow_pos_of_pos hZ0 _) hadm
  refine h1.trans ?_
  have h2 := hctl Wshort hsW j k v t V hV
  have hd : 0 ≤ CP*diagonalControl Ψ := mul_nonneg hCP (diagonalControl_nonneg Ψ)
  have hZp : 0 ≤ Z^(1+ε) := Real.rpow_nonneg hZ0.le _
  calc CP*diagonalControl Ψ*
        ((reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num) Wshort hsW j k v t).control SP)^2*
        (1+|t|+V)^dP*Z^(1+ε)
      = (CP*diagonalControl Ψ)*(((reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num)
          Wshort hsW j k v t).control SP)^2*(1+|t|+V)^dP)*Z^(1+ε) := by ring
    _ ≤ (CP*diagonalControl Ψ)*(DC*(sourceControl TC Wshort)^2*(1+|t|+V)^(dP+2*nC)*
          (1+‖v‖)^(2*nC))*Z^(1+ε) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hd) hZp
    _ = _ := by ring

/-- **Reflected leaf**: the natural reflection of the long factor (its per-`Z` instance `hR`
on the initial state `s`) with the children paid by the parent (`child_bound`) and the
discarded tail `htail`. -/
theorem reflected_leaf (W : ℝ → ℂ) (η η₀ : Character) (Q₀ : Id) (hQ₀ : internalQ Q₀ η₀ = Q₀)
    (Ψ : 𝓢(ℝ,ℂ)) (bΨ : ℝ) (hΨs : Function.support (Ψ:ℝ → ℂ) ⊆ Iic bΨ) (hΨ : ∀ x, 0 ≤ (Ψ x).re)
    (meshP ε : ℝ) (dP : ℕ) (SP : Finset (ℕ×ℕ)) (CP Z δ : ℝ) (hCP : 0 ≤ CP)
    (hZ : 1 < Z) (hδ : 0 ≤ δ) (hη : (η.modulus.absNorm:ℝ) ≤ Z^δ)
    (hP : InitialAffineAt (α:=α) M H hH (globalFace Bref Lref cref) W 2 (1/4) (9/4) bΨ meshP
      (33/50) (33/50) 1 1 ε Z η η₀ Q₀ dP SP CP)
    (nC : ℕ) (TC : Finset (ℕ×ℕ)) (DC : ℝ) (hDC : 0 ≤ DC)
    (hctl : ∀ (W' : 𝓢(ℝ,ℂ)) (hs : Function.support (W':ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (j k : Fin 2)
      (v t height : ℝ), 0 ≤ height →
      ((reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num) W' hs j k v t).control SP)^2*
        (1+|t|+height)^dP ≤
        DC*(sourceControl TC W')^2*(1+|t|+height)^(dP+2*nC)*(1+‖v‖)^(2*nC))
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ meshP) (hσ : ∀ i, σ i = 33/50)
    (hV : 0 ≤ V) (hfreq : ∀ i, |freq i| ≤ V)
    (F : Finset α) (epsR xi : ℝ) (nR : ℕ) (SR : Finset (ℕ×ℕ)) (CR DR : ℝ) (hDR : 0 ≤ DR)
    (s : NaturalState Z 0 bΨ) (hs : s = initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη)
    (hR : ∀ (Wlong Wshort : 𝓢(ℝ,ℂ)), Function.support (Wlong:ℝ→ℂ) ⊆ Icc (1/4) (9/4) →
      Function.support (Wshort:ℝ→ℂ) ⊆ Icc (1/4) (9/4) →
      ∀ (along bshort E : ℝ), s.width ≤ 2+along → 0 ≤ E →
      (∀ v : ℝ, ∀ j k : Fin 2, ∀ x ∈ Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z =>
            polynomial (naturalCharacter s.character z) false
              (scaleTest (fun y:ℝ => (annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) *
            polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Z^bshort) 0 t *
            ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (primePool M H 2 (Z^(w i)))
              (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤ E*(1+‖v‖)^(2*nC)) →
      radialEnergy (fun z =>
          polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (primePool M H 2 (Z^(w i)))
            (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        CR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^s.width))^epsR*
          (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*nR)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        DR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^s.width))^(2*epsR)*
          (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*nR)*Z^(-2*(1:ℝ))*
          radialEnergy (fun z =>
            polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
            ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (primePool M H 2 (Z^(w i)))
              (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale)
    (Wlong Wshort : 𝓢(ℝ,ℂ)) (hsl : Function.support (Wlong:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (hsW : Function.support (Wshort:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (along bshort ℓ : ℝ) (hxi : 0 ≤ xi) (hδ1 : δ ≤ 1) (hlong : 1/2 ≤ along)
    (hb : bshort ≤ ℓ) (hℓ : 0 ≤ ℓ)
    (hgate : ℓ + (1/2 + δ + xi) + Lref*(∑ i ∈ F, w i) ≤ Bref) (hcap : ∑ i ∈ F, w i ≤ cref)
    (Tail : ℝ)
    (htail : radialEnergy (fun z =>
            polynomial (naturalCharacter η z) false Wshort (Z^bshort) 0 t *
            ∏ i ∈ F, naturalSlot (naturalCharacter η z) (primePool M H 2 (Z^(w i)))
              (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
            (initialKeep η Q₀) Ψ Z ≤ Tail) :
    radialEnergy (fun z =>
        polynomial (naturalCharacter η z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter η z) false Wshort (Z^bshort) 0 t *
        ∏ i ∈ F, naturalSlot (naturalCharacter η z) (primePool M H 2 (Z^(w i)))
          (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
      (initialKeep η Q₀) Ψ Z ≤
      CR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^(1+δ)))^epsR*
          (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*nR)*
          (1+2*(max 0 (1+δ-along+xi)*Real.log Z))*
          (CP*diagonalControl Ψ*DC*(sourceControl TC Wshort)^2*(1+|t|+V)^(dP+2*nC)*Z^(1+ε)) +
        DR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^(1+δ)))^(2*epsR)*
          (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*nR)*Z^(-2*(1:ℝ))*Tail := by
  subst hs
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hE : 0 ≤ CP*diagonalControl Ψ*DC*(sourceControl TC Wshort)^2*(1+|t|+V)^(dP+2*nC)*Z^(1+ε) := by
    have := diagonalControl_nonneg Ψ
    have hZp : 0 ≤ Z^(1+ε) := Real.rpow_nonneg hZ0.le _
    positivity
  have hwidth : (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).width = 1+δ := rfl
  have hch := child_bound M H hH W η η₀ Q₀ hQ₀ Ψ bΨ hΨs hΨ meshP ε dP SP CP Z δ hCP hZ hδ hη hP
    nC TC DC hctl θ w σ freq t V hw hwm hσ hV hfreq Wshort hsW F along bshort xi ℓ hxi hlong hb hℓ
    hgate hcap
  have hrefl := hR Wlong Wshort hsl hsW along bshort _ (by rw [hwidth]; linarith) hE hch
  have heff : ∀ f : O → ℂ, radialEnergy f (initialKeep η Q₀) Ψ Z =
      radialEnergy f (effectiveState (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη)).radial.keep
        (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).radial.profile
        (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).radial.scale :=
    fun f => (radialEnergy_effective (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη).radial f).symm
  rw [heff] at htail ⊢
  rw [hwidth] at hrefl
  have hcoef : 0 ≤ DR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^(1+δ)))^(2*epsR)*
      (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*nR)*Z^(-2*(1:ℝ)) := by
    have h1 : 0 ≤ (max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^(1+δ)))^(2*epsR) :=
      Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
    have h2 : 0 ≤ Z^(-2*(1:ℝ)) := Real.rpow_nonneg hZ0.le _
    positivity
  exact hrefl.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail hcoef))

end

end
end Qrh.MarkedAnchor.Ordinary.Reference
