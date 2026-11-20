/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual independent-pair low P3 branch uniformly at every V>=H.
The earlier source caps are frozen at n/H,y/H; all live lengths stay original. -/
import Candidate.C092.transport.RegularColoredTerminalLeafLowUniform
import Candidate.C092.transport.RegularColoredTerminalLeafRows
import Candidate.C092.transport.RegularColoredTerminalLeafGeometry

set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
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
open QRH.Cycle092.StrongPair
open QRH.Record12518109Source QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.LowActual
local notation "O" => ActualEisensteinCubic.O

theorem terminal_low_high_selected {n y e Vmax : ℝ}
    (hmax : (98/100:ℝ) ≤ Vmax) (hVmax1 : 1≤ Vmax) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho:ℚ)) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ bufferMax : ℝ,0 < bufferMax ∧
    ∀ buffer : ℝ,0 < buffer → buffer ≤ bufferMax →
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ W : ℝ→ℂ,ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
      Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ → internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
      Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ → internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∀ old base : Character,
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),
    ∀ Cslot : ℝ,0 < Cslot → ∃ C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
    ∀ T : Finset Slot,∀ (θ θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr) (w σ σ₁ σ₂ v v₁ v₂ : Slot→ℝ)
      (tOld t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ)≤σ i) → (∀ i,σ i≤(33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) →
      (∑ i∈T,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow),
      (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
      (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
      (∀ u∈s,rowNorm u ≤ U^V) →
      (∀ u∈s,∀ i∈T,‖(originalMark rayM Hr hHr old base θ W U w σ v tOld) i u‖=
        ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
      (∀ u∈s,∀ i∈T,‖(originalMark rayM Hr hHr old base θ W U w σ v tOld) i u‖=
        ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
    finiteEnergyOn T (s.filter (fun u=> response U (Cslot*U^buffer) (fun i:T=> w i.val) (fun i=>‖(originalMark rayM Hr hHr old base θ W U w σ v tOld) i.val u‖^2) ≤ e)) η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ (originalMark rayM Hr hHr old base θ W U w σ v tOld)+
    finiteEnergyOn T (s.filter (fun u=> response U (Cslot*U^buffer) (fun i:T=> w i.val) (fun i=>‖(originalMark rayM Hr hHr old base θ W U w σ v tOld) i.val u‖^2) > (5002/10000:ℝ))) η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ (originalMark rayM Hr hHr old base θ W U w σ v tOld) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  classical
  obtain ⟨ml,hml,hlo⟩ := terminal_low_all_subsets hmax hβ cover hy0 hy1 hn0 hn1 he0 he1 hp
  obtain ⟨mh,hmh,hhi⟩ := terminal_high_selected_rows hy0 hy1 hn1 Vmax hVmax1
  refine ⟨min ml mh,lt_min hml hmh,?_⟩
  intro Slot _ _
  obtain ⟨bufferMax,hbMax,hlo⟩ := hlo Slot
  refine ⟨bufferMax,hbMax,?_⟩
  intro buffer hb hbSmall rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72 old base
  obtain ⟨degree,Sl,Cl,hCl,hlo⟩ := hlo buffer hb hbSmall rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  let controls := Sl∪{(0,0)}
  refine ⟨degree,controls,?_⟩
  intro Cslot hCslot
  obtain ⟨Ch,hCh,hhi⟩ := hhi Slot W hW.continuous hWs buffer Cslot hb hCslot old base
  let Clate := (max 1 Cslot)^(Fintype.card Slot)*Cl+Ch
  have hClate : 0< Clate := by unfold Clate;positivity
  refine ⟨Clate,hClate,?_⟩
  filter_upwards [hlo Cslot hCslot,hhi,Filter.eventually_gt_atTop (1:ℝ)] with U hlo hhi hU
  intro V hVmin hVmax T θ θ₁ θ₂ w σ σ₁ σ₂ v v₁ v₂ tOld t₁ t₂ height hw hwm hσlo hσhi
    hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY rows hk₁ hk₂ hy hm₁ hm₂
  have hlow := hlo V hVmin hVmax T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw
    (fun i=>(hwm i).trans (min_le_left _ _)) hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth
    p X₁ X₂ hX₁ hX₂ hXN hXY rows (originalMark rayM Hr hHr old base θ W U w σ v tOld)
    hk₁ hk₂ hy hm₁ hm₂
  have hhigh := hhi rayM Hr hHr V hVmin hVmax T θ w σ v tOld t₁ t₂ height hw
    (fun i=>(hwm i).trans (min_le_right _ _)) hσlo hσhi hh
    (hwidth.trans (sub_le_self _ (by norm_num [u]))) η₁ η₂ (internalQ Q₁ η₀₁) (internalQ Q₂ η₀₂)
    p X₁ X₂ hX₁ hX₂ hXN hXY rows hk₁ hk₂ hy
  have hctrl (S : Finset (ℕ×ℕ)) (hS : S⊆controls) : p.control S≤ p.control controls := by
    unfold Profiles.control
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hcl := hctrl Sl Finset.subset_union_left
  have hch := hctrl {(0,0)} Finset.subset_union_right
  have hp0 := p.control_nonneg Sl
  have hp1 := p.control_nonneg {(0,0)}
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 1≤1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hheightpow : 1≤(1+|t₁|+|t₂|+height)^degree := one_le_pow₀ hheight
  have hU0 := Real.rpow_nonneg (zero_lt_one.trans hU).le
    (V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))
  apply (add_le_add hlow hhigh).trans
  calc
    _ ≤ ((max 1 Cslot)^(Fintype.card Slot)*Cl)*QuadraticInitialBound.diagonalControl radialMajorant*
        (p.control controls)^2*(1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))+
      Ch*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
      apply add_le_add
      · gcongr
      · apply mul_le_mul_of_nonneg_right _ hU0
        simpa only [mul_one] using mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp1 hch 2) (mul_nonneg hCh.le hdΦ))
          hheightpow (by norm_num) (by positivity)
    _ = _ := by unfold Clate;ring

#print axioms terminal_low_high_selected
end
end QRH.Cycle092.RegularColoredForward
