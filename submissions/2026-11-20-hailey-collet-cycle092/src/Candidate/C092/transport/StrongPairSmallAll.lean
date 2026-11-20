/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairSmallMiddle
import Candidate.C092.transport.StrongPairSmallBridge
import Candidate.C092.transport.StrongPairSmallHigh

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.SmallCore

theorem small_pair_majorant_mono {a b C C' U exponent t₁ t₂ height : ℝ} {d d' : ℕ}
    {S S' : Finset (ℕ×ℕ)} (p : Profiles a b)
    (hU : 0 ≤ U) (hh : 0 ≤ height) (hC0 : 0 ≤ C) (hC : C ≤ C')
    (hd : d ≤ d') (hS : S ⊆ S') :
    C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S)^2*(1+|t₁|+|t₂|+height)^d*U^exponent ≤
      C'*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S')^2*(1+|t₁|+|t₂|+height)^d'*U^exponent := by
  have hc : p.control S ≤ p.control S':=by
    unfold Profiles.control
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hdiag:=QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hctrl:=p.control_nonneg S
  have hheight : 1 ≤ 1+|t₁|+|t₂|+height:=by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hpow:=pow_le_pow_right₀ hheight hd
  have hpU:=Real.rpow_nonneg hU exponent
  have hC0':=hC0.trans hC
  gcongr

/-- One early mesh and one fixed control set for every small radius. -/
theorem independent_all_small_radii {n y e : ℝ}
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ 3/4) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ,0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
      Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ → internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
      Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ → internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∀ Cslot : ℝ,0 ≤ Cslot →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ,0 ≤ V → V ≤ 98/100 →
    ∀ (J : Finset Slot) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr)
      (w σ₁ σ₂ v₁ v₂ : Slot→ℝ) (t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) →
      (∑ i∈J,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀ z∈s,initialKeep η₁ (internalQ Q₁ η₀₁) z.val) →
      (∀ z∈s,initialKeep η₂ (internalQ Q₂ η₀₂) z.val) →
      (∀ z∈s,rowNorm z ≤ U^V) →
      (∀ z∈s,∀ i∈J,‖mark i z‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) →
      (∀ z∈s,∀ i∈J,‖mark i z‖=
        ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
      (∀ z∈s,∀ i∈J,‖mark i z‖=
        ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
      finiteEnergyOn J s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  obtain ⟨mb,hmb,hbridge⟩:=independent_small_bridge hβ hy0 hy1 hn0 hn1 he0 he1
  obtain ⟨mh,hmh,hhigh⟩:=independent_small_high hβ hy0 hy1 hn0 hn1 he0 he1
  let mesh : ℝ:=min mb mh
  refine ⟨mesh,lt_min hmb hmh,?_⟩
  intro Slot _ _
  obtain ⟨bm,hbm,hmiddle⟩:=independent_small_middle hβ hy0 hy1 hn0 hn1 he0 he1 Slot
  obtain ⟨bb,hbb,hbridge⟩:=hbridge Slot
  obtain ⟨bh,hbh,hhigh⟩:=hhigh Slot
  let buffer : ℝ:=min bm (min bb bh)
  have hb : 0 < buffer:=lt_min hbm (lt_min hbb hbh)
  have hbm' : buffer ≤ bm:=min_le_left _ _
  have hbb' : buffer ≤ bb:=(min_le_right _ _).trans (min_le_left _ _)
  have hbh' : buffer ≤ bh:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72 Cslot hCslot
  obtain ⟨dm,Sm,Cm,hCm,hmiddle⟩:=hmiddle rayM Hr hHr bΦ (by linarith) hΦs η₁ η₂ η₀₁ η₀₂
    Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72 Cslot hCslot
  obtain ⟨db,Sb,Cb,hCb,hbridge⟩:=hbridge rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂
    Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72 Cslot hCslot
  obtain ⟨dh,Sh,Ch,hCh,hhigh⟩:=hhigh rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂
    Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72 Cslot hCslot
  let degree:=max dm (max db dh)
  let controls:=Sm∪(Sb∪Sh)
  let C:=Cm+Cb+Ch+1
  have hC : 0 < C:=by dsimp [C]; positivity
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hmiddle,hbridge,hhigh,eventually_ge_atTop (1:ℝ)] with U hmiddle hbridge hhigh hU
  intro V hV0 hV1 J θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hlow hmark₁ hmark₂
  have hlow' (b : ℝ) (hb' : buffer ≤ b) :
      ∀ z∈s,∀ i∈J,‖mark i z‖^2 ≤ (Cslot*U^b)*U^(e*w i) := by
    intro z hz i hi
    apply (hlow z hz i hi).trans
    have hp:=Real.rpow_le_rpow_of_exponent_le hU hb'
    gcongr
  have hmd : dm ≤ degree:=le_max_left _ _
  have hbd : db ≤ degree:=(le_max_left _ _).trans (le_max_right _ _)
  have hhd : dh ≤ degree:=(le_max_right _ _).trans (le_max_right _ _)
  have hmS : Sm ⊆ controls:=Finset.subset_union_left
  have hbS : Sb ⊆ controls:=(Finset.subset_union_left : Sb ⊆ Sb∪Sh).trans Finset.subset_union_right
  have hhS : Sh ⊆ controls:=(Finset.subset_union_right : Sh ⊆ Sb∪Sh).trans Finset.subset_union_right
  have hmC : Cm ≤ C:=by dsimp [C]; linarith
  have hbC : Cb ≤ C:=by dsimp [C]; linarith
  have hhC : Ch ≤ C:=by dsimp [C]; linarith
  by_cases hm : V ≤ 7/8
  · exact (hmiddle V hV0 hm J w t₁ t₂ height hw hh hwidth p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy
      (hlow' bm hbm')).trans (small_pair_majorant_mono p (zero_le_one.trans hU) hh hCm.le hmC hmd hmS)
  · by_cases hb' : V ≤ bridgeMax
    · have hVb : bridgeMin ≤ V:=by dsimp [bridgeMin]; linarith only [hm]
      exact (hbridge V hVb hb' J θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw
        (fun i=>(hwm i).trans (min_le_left _ _)) hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth p X₁ X₂
        hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy (hlow' bb hbb') hmark₁ hmark₂).trans
        (small_pair_majorant_mono p (zero_le_one.trans hU) hh hCb.le hbC hbd hbS)
    · have hVh : radiusMin ≤ V:=by change bridgeMax ≤ V; exact le_of_not_ge hb'
      exact (hhigh V hVh hV1 J θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw
        (fun i=>(hwm i).trans (min_le_right _ _)) hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth p X₁ X₂
        hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy (hlow' bh hbh') hmark₁ hmark₂).trans
        (small_pair_majorant_mono p (zero_le_one.trans hU) hh hCh.le hhC hhd hhS)

#print axioms independent_all_small_radii
end
end QRH.Cycle092.StrongPair
