/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual independent-pair low P3 branch uniformly at every V>=H.
The earlier source caps are frozen at n/H,y/H; all live lengths stay original. -/
import Candidate.C092.transport.StrongPairRegularTerminalLowUniformSource
import Candidate.C092.transport.StrongPairRegularTerminalZero
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
open QRH.Record12518109Source QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.LowActual
local notation "O" => ActualEisensteinCubic.O

theorem terminal_low_measured_pair_uniform {n y e Vmax : ℝ}
    (hmax : (98/100:ℝ) ≤ Vmax) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
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
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ Cslot : ℝ,0 < Cslot →
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
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
      (∀ u∈s,response U (Cslot*U^buffer) w (fun i=>‖mark i u‖^2) ≤ e) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      ((max 1 Cslot)^(Fintype.card Slot)*C)*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  obtain ⟨mesh,hm,hsource⟩ := terminal_low_pair_near_uniform hmax hβ cover hy0 hy1 hn0 hn1 he0 he1 hp
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  obtain ⟨bufferMax,hbMax,hsource⟩ := hsource Slot
  refine ⟨bufferMax,hbMax,?_⟩
  intro buffer hb hbSmall
  have hsource := hsource buffer hb hbSmall
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨F,hF,hzero⟩ := terminal_original_zero_bound W hW.continuous hWs
  obtain ⟨degree,controls,C,hC,hsource⟩ := hsource rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨degree,controls,C,hC,?_⟩
  intro Cslot hCslot
  have hsource := hsource Cslot hCslot.le
  have hcal := (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (F/Cslot))
  filter_upwards [hsource,hcal,eventually_gt_atTop (1:ℝ)] with U hsource hcal hU
  have hpay : F ≤ Cslot*U^buffer := by
    have h := (div_le_iff₀ hCslot).mp hcal
    linarith
  intro V hVmin hVmax θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth
    p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂ hresponse
  apply hsource V hVmin hVmax θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂
  intro u hu j
  have hz (k : Slot) (hk : w k=0) : ‖mark k u‖^2 ≤ Cslot*U^buffer := by
    rw [hm₂ u hu k]
    exact (hzero rayM Hr hHr U η₂ η₀₂ (fixedBadMask*idealGenerator 1) 1 u.val t₂ θ₂ w σ₂ v₂ k
      ((by norm_num : (0:ℝ) ≤ 33/50).trans (hσ₂lo k)) hk).trans hpay
  exact (response_le_iff_amplitudes w (fun k=>‖mark k u‖^2) hU
    (mul_pos hCslot (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)) hw (fun _=>sq_nonneg _) hz he0).mp
      (hresponse u hu) j

#print axioms terminal_low_measured_pair_uniform
end
end QRH.Cycle092.StrongPair
