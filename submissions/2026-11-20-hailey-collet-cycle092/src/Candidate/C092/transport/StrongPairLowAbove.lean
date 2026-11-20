/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual independent-pair low P3 branch uniformly at every V>=H.
The earlier source caps are frozen at n/H,y/H; all live lengths stay original. -/
import Candidate.C092.transport.StrongPairLowMetadata
import Candidate.C092.transport.LowActualUpperRadii

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Record12518109Source QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

theorem low_pair_above_H {n y e Vmax : ℝ}
    (hn0 : 0 ≤ n) (hy0 : 0 ≤ y) (hmax : (H:ℝ) ≤ Vmax)
    (hwidth : 0 < sourceWidth (n/(H:ℝ)) (y/(H:ℝ)))
    (hprev : PairOpenWidth (n/(H:ℝ)) (y/(H:ℝ)))
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho:ℚ)) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ,0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ W : ℝ→ℂ,ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
      Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ → internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
      Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ → internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∀ Cslot : ℝ,0 ≤ Cslot →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,(H:ℝ) ≤ V → V ≤ Vmax →
    ∀ (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr) (w σ₁ σ₂ v₁ v₂ : Slot→ℝ)
      (t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) →
      (∑ i,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
      (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
      (∀ u∈s,rowNorm u ≤ U^V) →
      (∀ u∈s,∀ i,‖mark i u‖=
        ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
      (∀ u∈s,∀ i,‖mark i u‖=
        ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
      (∀ u∈s,∀ i,‖mark i u‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4) := by
  obtain ⟨decrement,rounding,hd,hdw,hr,hfee⟩ := p3_early_rounding hwidth
  let l := sourceWidth (n/(H:ℝ)) (y/(H:ℝ))-decrement
  have hl : 0 < l := sub_pos.mpr hdw
  have hprevious := hprev l hl.le (sub_lt_self _ hd)
  let εsrc : ℝ := (rho:ℝ)/(16*Vmax)
  have hmaxpos : 0 < Vmax := H_real_bounds.1.trans_le hmax
  have hεsrc : 0 < εsrc := div_pos (by norm_num [rho]) (by positivity)
  have hεfee : Vmax*εsrc=(rho:ℝ)/16 := by dsimp [εsrc]; field_simp
  obtain ⟨sourceMesh,hsm,hsource⟩ := hprevious εsrc hεsrc
  let mesh := min rounding ((H:ℝ)*sourceMesh)
  have hm : 0 < mesh := lt_min hr (mul_pos H_real_bounds.1 hsm)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  let buffer : ℝ := (rho:ℝ)/(16*(1+(Fintype.card Slot:ℝ)))
  have hb : 0 < buffer := by dsimp [buffer]; norm_num [rho]; positivity
  have hbfee : buffer*(Fintype.card Slot:ℝ) ≤ (rho:ℝ)/16 := by
    have he : buffer*(16*(1+(Fintype.card Slot:ℝ)))=(rho:ℝ) := by dsimp [buffer]; field_simp
    nlinarith
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72 Cslot hCslot
  obtain ⟨degree,controls,Csrc,hCsrc,hsourceU⟩ := pair_radius_metadata hsource H_real_bounds.1
    Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  let C := (max 1 Cslot)^(Fintype.card Slot)*Csrc
  have hC : 0 < C := mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hCsrc
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsourceU,eventually_gt_atTop (1:ℝ)] with U hsourceU hU
  intro V hVH hVmax θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hwidthU p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hmark₁ hmark₂ hlow
  have hV : 0 < V := H_real_bounds.1.trans_le hVH
  obtain ⟨F,hF,hdel,_⟩ := select_before_rows w mesh (V*l) hw hwm hm.le (mul_nonneg hV.le hl.le)
  have hcard : (Finset.univ\F).card ≤ Fintype.card Slot := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ
  have herror : buffer*((Finset.univ\F).card:ℝ)+V*εsrc ≤ (rho:ℝ)/4 := by
    have hc : ((Finset.univ\F).card:ℝ) ≤ (Fintype.card Slot:ℝ) := by exact_mod_cast hcard
    have hh := mul_le_mul_of_nonneg_left hc hb.le
    have hvfee := mul_le_mul_of_nonneg_right hVmax hεsrc.le
    rw [hεfee] at hvfee
    linarith [show (0:ℝ) < (rho:ℝ) by norm_num [rho]]
  have hround : 2*(responseUpper:ℝ)*((H:ℝ)*decrement+mesh) ≤ (rho:ℝ) := by
    have hmround : mesh ≤ rounding := min_le_left _ _
    exact (mul_le_mul_of_nonneg_left (by linarith : (H:ℝ)*decrement+mesh ≤ (H:ℝ)*decrement+rounding)
      (by norm_num [responseUpper])).trans hfee
  have hpriceH := p3_paid_with_rounding (n:=n) he0 he1 hd.le hm.le hround hp
  have hcap : (H:ℝ)*l ≤ V*l := mul_le_mul_of_nonneg_right hVH hl.le
  change e*max 0 (sourceWidth n y-(u:ℝ)-(H:ℝ)*l+mesh) < (u:ℝ)-(rho:ℝ)/2 at hpriceH
  have hprice : e*max 0 (sourceWidth n y-(u:ℝ)-V*l+mesh) < (u:ℝ)-(rho:ℝ)/2+0 := by
    have hharg : sourceWidth n y-(u:ℝ)-V*l+mesh ≤ sourceWidth n y-(u:ℝ)-(H:ℝ)*l+mesh := by linarith only [hcap]
    have hh := (mul_le_mul_of_nonneg_left (max_le_max_left 0 hharg) he0).trans_lt hpriceH
    simpa only [add_zero] using hh
  have hwm' (i : Slot) : w i/V ≤ sourceMesh :=
    mesh_rescale H_real_bounds.1 hVH hsm.le (min_le_right _ _) (hwm i)
  have hnc : n/V ≤ n/(H:ℝ) := by
    apply (div_le_div_iff₀ hV H_real_bounds.1).2
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hVH)]
  have hyc : y/V ≤ y/(H:ℝ) := by
    apply (div_le_div_iff₀ hV H_real_bounds.1).2
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hVH)]
  have hNX : length (U^V) X₁ ≤ n/(H:ℝ) := by
    rw [length_rpow_base U X₁ V (zero_lt_one.trans hU)]
    exact (div_le_div_of_nonneg_right hXN hV.le).trans hnc
  have hYX : length (U^V) X₂ ≤ y/(H:ℝ) := by
    rw [length_rpow_base U X₂ V (zero_lt_one.trans hU)]
    exact (div_le_div_of_nonneg_right hXY hV.le).trans hyc
  have hE := low_pair_paid (allowance:=0) rayM Hr hHr (hsourceU V hVH) F θ₁ θ₂ w σ₁ σ₂ v₁ v₂
    t₁ t₂ height hw hwm' hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hF hU.le hV hCsrc.le hCslot he0
    hwidthU hdel hprice herror p X₁ X₂ hX₁ hX₂ hNX hYX s mark hk₁ hk₂ hy
    (fun u hu i _=>hmark₁ u hu i) (fun u hu i _=>hmark₂ u hu i)
    (fun u hu i _=>hlow u hu i)
  have hc : Cslot^(Finset.univ\F).card*Csrc ≤ C := by
    dsimp [C]
    apply mul_le_mul_of_nonneg_right _ hCsrc.le
    calc
      _ ≤ (max 1 Cslot)^(Finset.univ\F).card := by gcongr; exact le_max_right _ _
      _ ≤ (max 1 Cslot)^(Fintype.card Slot) := by gcongr; exact le_max_left _ _
  have hnonneg : 0 ≤ QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
      (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4) := by
    have hdΦ := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    positivity
  have hmul := mul_le_mul_of_nonneg_right hc hnonneg
  have hE' := hE.trans (show Cslot^(Finset.univ\F).card*(Csrc*QuadraticInitialBound.diagonalControl radialMajorant*
      (p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*U^(V+(u:ℝ)-(rho:ℝ)/4+0) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4) by
    simp only [add_zero]
    convert hmul using 1 <;> ring)
  exact hE'

#print axioms low_pair_above_H
end
end QRH.Cycle092.StrongPair
