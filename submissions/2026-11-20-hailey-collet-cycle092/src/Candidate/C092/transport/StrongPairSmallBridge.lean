/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairSmallBridgeSource
import Candidate.C092.transport.StrongPairSmallPayment

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

/-- Genuine independent pair with the duplicated short supplier on the bridge. -/
theorem independent_small_bridge {n y e : ℝ}
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
    ∀ V : ℝ,bridgeMin ≤ V → V ≤ bridgeMax →
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
  obtain ⟨ms,hms,hsource⟩:=independent_bridge_distinct_source hβ
  let mesh : ℝ:=min (bridgeMin*ms) (1/100000)
  have hrad : 0 < bridgeMin:=by norm_num [bridgeMin]
  have hm : 0 < mesh:=lt_min (mul_pos hrad hms) (by norm_num)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  let buffer : ℝ:=1/(10000*(1+(Fintype.card Slot:ℝ)))
  have hb : 0 < buffer:=by dsimp [buffer]; positivity
  have hfee : buffer*(Fintype.card Slot:ℝ) ≤ 1/10000:=by
    have heq : buffer*(10000*(1+(Fintype.card Slot:ℝ)))=1:=by dsimp [buffer]; field_simp
    nlinarith only [heq,hb]
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72 Cslot hCslot
  obtain ⟨d,S,C₀,hC₀,hsrc⟩:=hsource Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂
    Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72
  let A : ℝ:=(max 1 Cslot)^(Fintype.card Slot)
  have hA : 0 < A:=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨d,S,A*C₀,mul_pos hA hC₀,?_⟩
  filter_upwards [hsrc,eventually_gt_atTop (1:ℝ)] with U hsrc hU
  intro V hV0 hV1 J θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hlow hmark₁ hmark₂
  have hUp : 0 < U:=zero_lt_one.trans hU
  have hV : 0 < V:=hrad.trans_le hV0
  obtain ⟨T,hTJ,hTwidth,hdelete⟩:=small_select_on J w mesh (V*bridgeWidth/2)
    hw hwm hm.le (by positivity [bridge_width_positive])
  have hTquota : 2*(∑ i∈T,w i) ≤ V*bridgeWidth:=by linarith
  have hnhi : n ≤ 1:=by norm_num [sourceRatio,sourceY] at hn1 hy1; linarith
  have hyhi : y ≤ 1:=hy1.trans (by norm_num [sourceY])
  have hbox : Box n y 0 (length U X₁) (length U X₂) 0:=
    ⟨length_nonneg _ _ hU,length_nonneg _ _ hU,Or.inl ⟨hXN,hXY⟩,le_rfl,le_rfl⟩
  have hlengths:=ordinary_lengths_below_U hU hnhi hyhi hbox
  have hshort : length (U^V) X₂ ≤ bridgeCap:=by
    rw [length_rpow_base U X₂ V hUp]
    apply (div_le_iff₀ hV).mpr
    have hvb:=mul_le_mul_of_nonneg_left hV0
      (show 0 ≤ bridgeCap by norm_num [bridgeCap,bridgeMin,sourceY])
    have heq : bridgeCap*bridgeMin=sourceY:=by norm_num [bridgeCap,bridgeMin]
    linarith
  have hwm' (i : Slot) : w i/V ≤ ms:=mesh_rescale hrad hV0 hms.le (min_le_left _ _) (hwm i)
  have hsE:=hsrc V hV0 hV1 T θ₂ w σ₂ v₂ t₁ t₂ height hw hwm' hσ₂lo hσ₂hi hh hv₂
    hTquota p X₁ X₂ hX₁ hX₂ hlengths.1 hshort s hk₁ hk₂ hy
  have hretained : finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C₀*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S)^2*
        (1+|t₁|+|t₂|+height)^d*U^(V+1/1000) := by
    apply le_trans (le_of_eq ?_) hsE
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    exact Finset.prod_congr rfl (fun i hi=>congrArg (fun r:ℝ=>r^2) (hmark₂ z hz i (hTJ hi)))
  have hcard : ((J\T).card:ℝ) ≤ (Fintype.card Slot:ℝ):=by exact_mod_cast Finset.card_le_univ (J\T)
  have hbuf : buffer*((J\T).card:ℝ) ≤ 1/10000:=
    (mul_le_mul_of_nonneg_left hcard hb.le).trans hfee
  have hpaid:=bridge_paid hV0 hV1 he0 he1
    (hwidth.trans (original_width_cap_sharp hy0 hy1 hn0)) hm.le (min_le_right _ _) hbuf
  have hcost:=mul_le_mul_of_nonneg_left hdelete he0
  have hdiag:=QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hp:=small_payment J T hTJ s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark
    Cslot U e buffer V (1/1000)
    (V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))
    (C₀*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S)^2*
      (1+|t₁|+|t₂|+height)^d) w hU.le hCslot (by positivity)
    (fun z hz i hi=>hlow z hz i (Finset.mem_sdiff.mp hi).1) hretained (by linarith)
  convert hp using 1 <;> dsimp [A] <;> ring

#print axioms independent_small_bridge
end
end QRH.Cycle092.StrongPair
