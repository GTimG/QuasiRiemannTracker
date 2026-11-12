/- Copyright (c) 2026 Sil. Apache-2.0.
The uniform leaf bound of the reference lane: direct payment when the long factor has
`log_Z`-length `≤ 1/2`, natural reflection otherwise (the reflected dual factor then has length
`≤ 1/2 + δ + ξ`), both in the parent face `G(.99, 49/20, .14)` by the gate
`ℓ + 1/2 + δ + ξ + L_ref c ≤ B_ref`. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Reference.LeafBound

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

/-- The total leaf constant. -/
def Ktot (CP CR DR DC CD Cerr dg : ℝ) : ℝ := CP*dg*CD^4 + CR*CP*dg*DC + DR*Cerr*dg

theorem final_step (K x h Z : ℝ) (m J : ℕ) (e1 e2 : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x) (hh : 1 ≤ h)
    (hmJ : m ≤ J) (hZ : 1 ≤ Z) (he : e1 ≤ e2) : K*x*h^m*Z^e1 ≤ K*x*h^J*Z^e2 := by
  have h1 : h^m ≤ h^J := pow_le_pow_right₀ hh hmJ
  have h2 : Z^e1 ≤ Z^e2 := Real.rpow_le_rpow_of_exponent_le hZ he
  have hZe1 : 0 ≤ Z^e1 := Real.rpow_nonneg (by linarith) _
  have hhJ : 0 ≤ h^J := pow_nonneg (by linarith) _
  calc K*x*h^m*Z^e1 ≤ K*x*h^J*Z^e1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hx)) hZe1
    _ ≤ K*x*h^J*Z^e2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hK hx) hhJ)

section
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Id) [NeZero M]
local instance instFiniteQuotLeafCore : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

set_option maxHeartbeats 2000000 in
/-- **Leaf bound**, second factor short. -/
theorem leaf_core (W : ℝ → ℂ) (η η₀ : Character) (Q₀ : Id) (hQ₀ : internalQ Q₀ η₀ = Q₀)
    (Ψ : 𝓢(ℝ,ℂ)) (bΨ : ℝ) (hΨs : Function.support (Ψ:ℝ → ℂ) ⊆ Iic bΨ) (hΨ : ∀ x, 0 ≤ (Ψ x).re)
    (meshP εP : ℝ) (hεP : 0 ≤ εP) (dP : ℕ) (SP : Finset (ℕ×ℕ)) (CP Z δ : ℝ) (hCP : 0 ≤ CP)
    (hZ : 1 < Z) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : (η.modulus.absNorm:ℝ) ≤ Z^δ)
    (hP : InitialAffineAt (α:=α) M H hH (globalFace Bref Lref cref) W 2 (1/4) (9/4) bΨ meshP
      (33/50) (33/50) 1 1 εP Z η η₀ Q₀ dP SP CP)
    (nC : ℕ) (TC : Finset (ℕ×ℕ)) (DC : ℝ) (hDC : 0 ≤ DC)
    (hctl : ∀ (W' : 𝓢(ℝ,ℂ)) (hs : Function.support (W':ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (j k : Fin 2)
      (v t height : ℝ), 0 ≤ height →
      ((reflectionProfiles (by norm_num : (0:ℝ) < 1/4) le_rfl (by norm_num) W' hs j k v t).control SP)^2*
        (1+|t|+height)^dP ≤
        DC*(sourceControl TC W')^2*(1+|t|+height)^(dP+2*nC)*(1+‖v‖)^(2*nC))
    (epsR xi : ℝ) (hepsR : 0 ≤ epsR) (hepsR2 : epsR ≤ 1/2) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (nR : ℕ) (SR : Finset (ℕ×ℕ)) (CR DR : ℝ) (hCR : 0 ≤ CR) (hDR : 0 ≤ DR)
    (hRZ : ReflectionAt bΨ epsR xi 1 2 nC nR SR CR DR Z)
    (nD : ℕ) (TD : Finset (ℕ×ℕ)) (CD : ℝ) (hCD : 0 ≤ CD)
    (hnp : ∀ (W' : 𝓢(ℝ,ℂ)) (hs : Function.support (W':ℝ→ℂ) ⊆ Icc (1/4) (9/4)) (t : ℝ),
      SP.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W' (1/4) (9/4) (by norm_num) hs (W'.smooth ⊤) t) ≤
        CD*TD.sup (schwartzSeminormFamily ℝ ℝ ℂ) W'*(1+‖t‖)^nD)
    (control : Finset (ℕ×ℕ)) (hSR : SR ⊆ control) (hTC : TC ⊆ control) (hTD : TD ⊆ control)
    (h00 : ((0:ℕ),(0:ℕ)) ∈ control)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ meshP) (hσ : ∀ i, σ i = 33/50)
    (hV : 0 ≤ V) (hfreq : ∀ i, |freq i| ≤ V)
    (Cerr : ℝ) (hCerr : 0 ≤ Cerr)
    (htail : ∀ (A : Finset α) (Ws : 𝓢(ℝ,ℂ)), Function.support (Ws:ℝ→ℂ) ⊆ Icc (1/4) (9/4) →
      ∀ bshort : ℝ,
      radialEnergy (fun z => polynomial (naturalCharacter η z) false Ws (Z^bshort) 0 t *
          ∏ i ∈ A, naturalSlot (naturalCharacter η z) (primePool M H 2 (Z^(w i)))
            (heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (Z^(w i)))
        (initialKeep η Q₀) Ψ Z ≤
        Cerr*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Ws)^2*diagonalControl Ψ*max 1 Z*Z^bshort*
          ∏ i ∈ A, Z^(w i))
    (ℓ c : ℝ) (hℓ : 0 ≤ ℓ) (hgate : ℓ + (1/2+δ+xi) + Lref*c ≤ Bref) (hc : c ≤ cref)
    (hℓc : ℓ + c ≤ 1)
    (hcond : (fixedConductorFactor:ℝ)*bΨ ≤ Z) (hbΨ : 0 ≤ bΨ) (hlog : 1 + 6*Real.log Z ≤ Z^epsR)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Icc (1/4) (9/4))
    (A : Finset α) (hA : ∑ i ∈ A, w i ≤ c) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hshort : X₂ ≤ Z^ℓ) :
    nativeLeaf M H hH W η₀ θ Z w σ freq t η (initialKeep η Q₀) Ψ Z W₁ W₂ t t A X₁ X₂ ≤
      Ktot CP CR DR DC CD Cerr (diagonalControl Ψ)*
        (sourceControl control W₁*sourceControl control W₂)^2*
        (1+|t|+V)^(dP+2*nC+2*nR+4*nD)*Z^(1+εP+4*epsR) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hdg := diagonalControl_nonneg Ψ
  set dg := diagonalControl Ψ with hdg_def
  set h := 1+|t|+V with hh_def
  set J := dP+2*nC+2*nR+4*nD with hJ_def
  set k1 := sourceControl control W₁ with hk1
  set k2 := sourceControl control W₂ with hk2
  have hk10 : 0 ≤ k1 := sourceControl_nonneg _ _
  have hk20 : 0 ≤ k2 := sourceControl_nonneg _ _
  have hh1 : 1 ≤ h := by have := abs_nonneg t; linarith
  have hh0 : 0 ≤ h := zero_le_one.trans hh1
  have hth : 1+‖t‖ ≤ h := by rw [Real.norm_eq_abs]; linarith
  have hsA0 : 0 ≤ ∑ i ∈ A, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hL : (0:ℝ) ≤ Lref := by norm_num [Lref]
  have hLA : Lref*(∑ i ∈ A, w i) ≤ Lref*c := mul_le_mul_of_nonneg_left hA hL
  have hb : Real.logb Z X₂ ≤ ℓ := (Real.logb_le_iff_le_rpow hZ hX₂).mpr hshort
  have hZpow : Z^(1+εP) ≤ Z^(1+εP+4*epsR) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hKt : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      Ktot CP CR DR DC CD Cerr dg = x + y + z → y + z ≤ Ktot CP CR DR DC CD Cerr dg := by
    intro x y z hx _ _ he; rw [he]; linarith
  by_cases hlong : Real.logb Z X₁ ≤ 1/2
  · -- direct payment
    have hl1 : length Z X₁ ≤ 1/2 := length_le_of_logb Z X₁ (1/2) hZ hX₁ (by norm_num) hlong
    have hl2 : length Z X₂ ≤ ℓ := length_le_of_logb Z X₂ ℓ hZ hX₂ hℓ hb
    have hadm := (globalFace_admissible_iff (length_nonneg Z X₁ hZ) (length_nonneg Z X₂ hZ)
      hsA0 hL (B := Bref) (cap := cref) (M := 1)).mpr
      ⟨by rw [mul_one]; linarith, by rw [mul_one]; linarith⟩
    have hd := direct_leaf M H hH W η η₀ Q₀ hQ₀ Ψ bΨ hΨs hΨ meshP εP dP SP CP Z hZ hP
      θ w σ freq t V hw hwm hσ hV hfreq W₁ W₂ hs₁ hs₂ t t A X₁ X₂ hX₁ hX₂ hadm
    have hc := independent_control_le SP TD control nD CD hCD hnp hTD W₁ W₂ hs₁ hs₂ t h hth
    refine hd.trans ?_
    have hK : 0 ≤ CP*dg*CD^4 := by positivity
    have hX : 0 ≤ (k1*k2)^2 := by positivity
    have hZ1e : 0 ≤ Z^(1+εP) := Real.rpow_nonneg hZ0.le _
    have hcd : (CP*dg)*((independentProfiles (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t t).control SP)^2 ≤
        (CP*dg)*(CD^4*(k1*k2)^2*h^(4*nD)) := mul_le_mul_of_nonneg_left hc (mul_nonneg hCP hdg)
    have hstep1 : CP*dg*((independentProfiles (by norm_num : (0:ℝ) < 1/4) W₁ W₂ hs₁ hs₂ t t).control SP)^2*
          h^dP*Z^(1+εP) ≤ (CP*dg*CD^4)*(k1*k2)^2*h^(4*nD+dP)*Z^(1+εP) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (pow_nonneg hh0 dP)) hZ1e
      refine this.trans (le_of_eq ?_)
      rw [pow_add]; ring
    refine hstep1.trans ((final_step _ _ h Z (4*nD+dP) J (1+εP) (1+εP+4*epsR) hK hX hh1
      (by omega) hZ.le (by linarith)).trans ?_)
    have hY : 0 ≤ (k1*k2)^2*h^J*Z^(1+εP+4*epsR) := by positivity
    have e : Ktot CP CR DR DC CD Cerr dg*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) =
        (CP*dg*CD^4)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) +
        (CR*CP*dg*DC)*((k1*k2)^2*h^J*Z^(1+εP+4*epsR)) +
        (DR*Cerr*dg)*((k1*k2)^2*h^J*Z^(1+εP+4*epsR)) := by unfold Ktot; ring
    rw [e]
    have h1 : 0 ≤ (CR*CP*dg*DC)*((k1*k2)^2*h^J*Z^(1+εP+4*epsR)) := mul_nonneg (by positivity) hY
    have h2 : 0 ≤ (DR*Cerr*dg)*((k1*k2)^2*h^J*Z^(1+εP+4*epsR)) := mul_nonneg (by positivity) hY
    linarith
  · -- natural reflection of the long factor
    have hlong' : 1/2 ≤ Real.logb Z X₁ := le_of_lt (not_le.mp hlong)
    have hXl : Z^(Real.logb Z X₁) = X₁ := Real.rpow_logb hZ0 hZ.ne' hX₁
    have hXs : Z^(Real.logb Z X₂) = X₂ := Real.rpow_logb hZ0 hZ.ne' hX₂
    have hgateA : ℓ + (1/2+δ+xi) + Lref*(∑ i ∈ A, w i) ≤ Bref := by linarith
    have hcapA : ∑ i ∈ A, w i ≤ cref := hA.trans hc
    have hR := reflected_leaf M H hH W η η₀ Q₀ hQ₀ Ψ bΨ hΨs hΨ meshP εP dP SP CP Z δ hCP hZ hδ hη hP
      nC TC DC hDC hctl θ w σ freq t V hw hwm hσ hV hfreq A epsR xi nR SR CR DR hDR
      (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη) rfl
      (fun Wl Ws hl hs along bshort E h1 h2 h3 =>
        hRZ 0 (initialState η Q₀ Ψ bΨ Z δ hZ.le hδ hΨs hΨ hη) Wl Ws hl hs α A
          (fun i => primePool M H 2 (Z^(w i)))
          (fun i => heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t)
          (fun i => Z^(w i)) t along bshort E h1 h2 h3)
      W₁ W₂ hs₁ hs₂ (Real.logb Z X₁) (Real.logb Z X₂) ℓ hxi hδ1 hlong' hb hℓ hgateA hcapA _
      (htail A W₂ hs₂ (Real.logb Z X₂))
    rw [hXl, hXs] at hR
    unfold nativeLeaf leafEnergy leafRow
    refine hR.trans ?_
    -- scalar bookkeeping
    have hfc : (0:ℝ) ≤ (fixedConductorFactor:ℝ)*bΨ := mul_nonneg (Nat.cast_nonneg _) hbΨ
    have m1 := conductor_pow_le _ Z δ epsR hfc hZ.le hcond hδ hδ1 hepsR
    have m2 := conductor_pow_le _ Z δ (2*epsR) hfc hZ.le hcond hδ hδ1 (by linarith)
    have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ.le
    have hlg : 1+2*(max 0 (1+δ-Real.logb Z X₁+xi)*Real.log Z) ≤ Z^epsR := by
      have hm : max 0 (1+δ-Real.logb Z X₁+xi) ≤ 3 := max_le (by norm_num) (by linarith)
      have := mul_le_mul_of_nonneg_right hm hlogZ
      linarith
    have ha : SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁ ≤ k1 :=
      Seminorm.le_def.mp (Finset.sup_mono hSR) W₁
    have hb2 : sourceControl TC W₂ ≤ k2 := Seminorm.le_def.mp (Finset.sup_mono hTC) W₂
    have hc0 : (schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₂ ≤ k2 :=
      Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) h00) W₂
    have hq : (1+‖t‖)^(2*nR) ≤ h^(2*nR) := pow_le_pow_left₀ (by positivity) hth _
    have hprodZ : ∏ i ∈ A, Z^(w i) ≤ Z^c := by
      rw [← Real.rpow_sum_of_pos hZ0]; exact Real.rpow_le_rpow_of_exponent_le hZ.le hA
    have ha0 : 0 ≤ SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁ := apply_nonneg _ _
    have hb20 : 0 ≤ sourceControl TC W₂ := sourceControl_nonneg _ _
    -- the reflected main term
    have T1 : CR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^(1+δ)))^epsR*
          (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)^2*(1+‖t‖)^(2*nR)*
          (1+2*(max 0 (1+δ-Real.logb Z X₁+xi)*Real.log Z))*
          (CP*dg*DC*(sourceControl TC W₂)^2*h^(dP+2*nC)*Z^(1+εP)) ≤
        (CR*CP*dg*DC)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) := by
      have hlg0 : 0 ≤ 1+2*(max 0 (1+δ-Real.logb Z X₁+xi)*Real.log Z) := by
        have := le_max_left 0 (1+δ-Real.logb Z X₁+xi); positivity
      calc _ ≤ CR*Z^(3*epsR)*k1^2*h^(2*nR)*Z^epsR*(CP*dg*DC*k2^2*h^(dP+2*nC)*Z^(1+εP)) := by
            gcongr
        _ = (CR*CP*dg*DC)*(k1*k2)^2*(h^(2*nR)*h^(dP+2*nC))*(Z^(3*epsR)*Z^epsR*Z^(1+εP)) := by ring
        _ = (CR*CP*dg*DC)*(k1*k2)^2*h^(2*nR+(dP+2*nC))*Z^(3*epsR+epsR+(1+εP)) := by
            rw [← pow_add, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        _ ≤ (CR*CP*dg*DC)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) :=
            final_step _ _ h Z _ J _ _ (by positivity) (by positivity) hh1 (by omega) hZ.le
              (by linarith)
    -- the discarded tail
    have hmaxZ' : max 1 Z ≤ Z^(1:ℝ) := by rw [Real.rpow_one]; exact max_le hZ.le le_rfl
    have hc00 : 0 ≤ (schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₂ := apply_nonneg _ _
    have T2 : DR*(max 1 ((fixedConductorFactor:ℝ)*bΨ*Z^(1+δ)))^(2*epsR)*
          (SR.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)^2*(1+‖t‖)^(2*nR)*Z^(-2*(1:ℝ))*
          (Cerr*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₂)^2*dg*max 1 Z*X₂*
            ∏ i ∈ A, Z^(w i)) ≤
        (DR*Cerr*dg)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) := by
      have hZm2 : 0 ≤ Z^(-2*(1:ℝ)) := Real.rpow_nonneg hZ0.le _
      calc _ ≤ DR*Z^(3*(2*epsR))*k1^2*h^(2*nR)*Z^(-2*(1:ℝ))*
              (Cerr*k2^2*dg*Z^(1:ℝ)*Z^ℓ*Z^c) := by
            gcongr
        _ = (DR*Cerr*dg)*(k1*k2)^2*h^(2*nR)*
              (Z^(3*(2*epsR))*Z^(-2*(1:ℝ))*Z^(1:ℝ)*Z^ℓ*Z^c) := by ring
        _ = (DR*Cerr*dg)*(k1*k2)^2*h^(2*nR)*Z^(3*(2*epsR)+(-2*(1:ℝ))+1+ℓ+c) := by
            rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        _ ≤ (DR*Cerr*dg)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) :=
            final_step _ _ h Z _ J _ _ (by positivity) (by positivity) hh1 (by omega) hZ.le
              (by linarith)
    have hsum := add_le_add T1 T2
    refine hsum.trans ?_
    have hX : 0 ≤ (k1*k2)^2*h^J*Z^(1+εP+4*epsR) := by positivity
    have e : Ktot CP CR DR DC CD Cerr dg*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) =
        (CP*dg*CD^4)*((k1*k2)^2*h^J*Z^(1+εP+4*epsR)) +
        (CR*CP*dg*DC)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) +
        (DR*Cerr*dg)*(k1*k2)^2*h^J*Z^(1+εP+4*epsR) := by unfold Ktot; ring
    rw [e]
    have : 0 ≤ (CP*dg*CD^4)*((k1*k2)^2*h^J*Z^(1+εP+4*epsR)) := mul_nonneg (by positivity) hX
    linarith

end

end
end Qrh.MarkedAnchor.Ordinary.Reference
