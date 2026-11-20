/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual independent-pair low P3 branch uniformly at every V>=H.
The earlier source caps are frozen at n/H,y/H; all live lengths stay original. -/
import Candidate.C092.transport.StrongPairRegularTerminalLowUniform
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

theorem terminal_low_measured_on {n y e Vmax : ℝ}
    (hmax : (98/100:ℝ) ≤ Vmax) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho:ℚ)) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],∀ T : Finset Slot,
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
      (∑ i∈T,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
      (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
      (∀ u∈s,rowNorm u ≤ U^V) →
      (∀ u∈s,∀ i∈T,‖mark i u‖=
        ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
      (∀ u∈s,∀ i∈T,‖mark i u‖=
        ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
      (∀ u∈s,response U (Cslot*U^buffer) (fun i:T=>w i.val) (fun i=>‖mark i.val u‖^2) ≤ e) →
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      ((max 1 Cslot)^(T.card)*C)*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  obtain ⟨mesh,hm,hsource⟩ := terminal_low_measured_pair_uniform hmax hβ cover hy0 hy1 hn0 hn1 he0 he1 hp
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ T
  obtain ⟨bufferMax,hbMax,hsource⟩ := hsource T
  refine ⟨bufferMax,hbMax,?_⟩
  intro buffer hb hbSmall rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨degree,controls,C,hC,hsource⟩ := hsource buffer hb hbSmall rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨degree,controls,C,hC,?_⟩
  intro Cslot hCslot
  filter_upwards [hsource Cslot hCslot] with U hsource
  intro V hVmin hVmax θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂ hresponse
  rw [terminal_energy_subtype]
  have he := hsource V hVmin hVmax (fun i:T=>θ₁ i.val) (fun i:T=>θ₂ i.val)
    (fun i:T=>w i.val) (fun i:T=>σ₁ i.val) (fun i:T=>σ₂ i.val)
    (fun i:T=>v₁ i.val) (fun i:T=>v₂ i.val) t₁ t₂ height
    (fun i=>hw i.val) (fun i=>hwm i.val) (fun i=>hσ₁lo i.val) (fun i=>hσ₁hi i.val)
    (fun i=>hσ₂lo i.val) (fun i=>hσ₂hi i.val) hh (fun i=>hv₁ i.val) (fun i=>hv₂ i.val)
    (by simpa only [Finset.sum_coe_sort] using hwidth)
    p X₁ X₂ hX₁ hX₂ hXN hXY rows (fun i:T=>mark i.val) hk₁ hk₂ hy
    (fun u hu i=>hm₁ u hu i.val i.property) (fun u hu i=>hm₂ u hu i.val i.property) hresponse
  simpa only [Fintype.card_coe] using he

#print axioms terminal_low_measured_on
end
end QRH.Cycle092.RegularColoredForward
