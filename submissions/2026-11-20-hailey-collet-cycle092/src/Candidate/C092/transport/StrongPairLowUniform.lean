/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual original-mark low source on the detector's fixed witness pairs.
Both independent ordinary anchors use the same original kept finite rows. -/
import Candidate.C092.transport.StrongPairLowActual

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
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.LowActual QRH.Cycle092.MediumReplace.Source
local notation "O" => ActualEisensteinCubic.O

/-- The entire early finite witness dictionary shares one degree, control
set, constant and eventual threshold before ANY later row-dependent label. -/
theorem low_original_witness_pairs_uniform {n y e Vmax : ℝ}
    (hmax : (98/100:ℝ) ≤ Vmax) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho:ℚ)) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ,0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ W : ℝ→ℂ,ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η base : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q base ≠ 0 → internalQ Q base ≠ ⊤ → internalQ Q base ≤ Ideal.span {(72:O)} →
    ∀ Cslot : ℝ,0 ≤ Cslot →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ j₁ j₂ : Option (RayQuotient.Characters rayM Hr × RayQuotient.Characters rayM Hr),
    ∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
    ∀ (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
      (tOld t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ i) → (∀ i,σ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v i| ≤ height) → (∑ i,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ s : Finset FreeRow,(∀ u∈s,initialKeep η (internalQ Q base) u.val) →
      (∀ u∈s,rowNorm u ≤ U^V) →
      (∀ u∈s,∀ i,‖originalMark rayM Hr hHr η base θ W U w σ v tOld i u‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) →
    finiteEnergy s (witnessBase rayM Hr hHr η base j₁) (witnessBase rayM Hr hHr η base j₂)
      (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ (originalMark rayM Hr hHr η base θ W U w σ v tOld) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height))^degree*
        U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  obtain ⟨mesh,hm,hsource⟩ := low_original_witness_pairs hmax hβ cover hy0 hy1 hn0 hn1 he0 he1 hp
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  obtain ⟨buffer,hb,hsource⟩ := hsource Slot
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η base Q hQray hQ0 hQtop hQ72 Cslot hCslot
  let Label := Option (RayQuotient.Characters rayM Hr × RayQuotient.Characters rayM Hr)
  have hs := fun j : Label×Label=>hsource rayM Hr hHr W hW hWs bΦ hbΦ hΦs η base j.1 j.2 Q
    hQray hQ0 hQtop hQ72 Cslot hCslot
  choose d S C hC hsource using hs
  let degree := Finset.univ.sup d
  let controls := Finset.univ.biUnion S
  let constant := (∑ j : Label×Label,C j)+1
  have hconstant : 0 < constant := by
    have hh : 0 ≤ ∑ j : Label×Label,C j := Finset.sum_nonneg (fun j _=>(hC j).le)
    dsimp [constant]
    linarith
  refine ⟨degree,controls,constant,hconstant,?_⟩
  have hUall := Filter.eventually_all.mpr hsource
  filter_upwards [hUall,eventually_gt_atTop (1:ℝ)] with U hsource hU
  intro j₁ j₂ V hVmin hVmax θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hv hwidth
    p X₁ X₂ hX₁ hX₂ hXN hXY s hk hy hlow
  let j : Label×Label := (j₁,j₂)
  have hE := hsource j V hVmin hVmax θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hv
    hwidth p X₁ X₂ hX₁ hX₂ hXN hXY s hk hy hlow
  have hd : d j ≤ degree := Finset.le_sup (Finset.mem_univ j)
  have hS : S j ⊆ controls := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,ha⟩
  have hconst : C j ≤ constant := by
    have hx := Finset.single_le_sum (fun q _=>(hC q).le) (Finset.mem_univ j)
    dsimp [constant]
    linarith
  have hc : p.control (S j) ≤ p.control controls := by
    unfold Profiles.control
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hp0 := p.control_nonneg (S j)
  have hp1 := p.control_nonneg controls
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 1 ≤ 1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height) := by
    linarith [abs_nonneg t₁,abs_nonneg t₂,abs_nonneg tOld]
  have hp := pow_le_pow_right₀ hheight hd
  have hC0 := (hC j).le
  have hC0' := hconstant.le
  have hpow := Real.rpow_nonneg (zero_le_one.trans hU.le) (V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))
  exact hE.trans (by gcongr)

#print axioms low_original_witness_pairs_uniform
end
end QRH.Cycle092.StrongPair
