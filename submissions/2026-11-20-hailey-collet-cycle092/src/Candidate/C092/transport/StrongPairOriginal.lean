/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual independent-character native starting strip, on the entire
original common mark product, with no mark-presentation hypotheses. -/
import Candidate.C092.transport.StrongPairAll
import Candidate.C092.transport.StrongPairInduction

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
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary QRH.Cycle092.PairMarkAnchor
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

/-- A proved genuine base source on all original finite rows. The source is
chosen before live arrays and heights; the two fourths are applied only after
the exact whole-slot partition. Bounded marks use a fixed absolute constant.
Its sole arithmetic row gates are the two actual exceptional exclusions. -/
theorem native_original_pair_source
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y l : ℝ} (hy : sourceY ≤ y) (hy' : y ≤ sourceY/(H:ℝ))
    (hn : y ≤ n) (hr : n ≤ sourceRatio*y) (hl0 : 0 ≤ l) (hl : l < sourceWidth n y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ W : ℝ→ℂ, ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (old base η₁ η₂ : Character) (Q₁ Q₂ : Ideal O),
      Q₁ ≤ rayM → internalQ Q₁ (anchoredBase base old η₁) ≠ 0 →
      internalQ Q₁ (anchoredBase base old η₁) ≠ ⊤ →
      internalQ Q₁ (anchoredBase base old η₁) ≤ Ideal.span {(72:O)} →
      Q₂ ≤ rayM → internalQ Q₂ (anchoredBase base old η₂) ≠ 0 →
      internalQ Q₂ (anchoredBase base old η₂) ≠ ⊤ →
      internalQ Q₂ (anchoredBase base old η₂) ≤ Ideal.span {(72:O)} →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ Z : ℝ in atTop,
    ∀ (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
      (tOld t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ i) → (∀ i,σ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v i| ≤ height) → (∑ i,w i) ≤ l →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ n → length Z X₂ ≤ y →
    ∀ s : Finset FreeRow,
      (∀ u∈s,initialKeep η₁ (internalQ Q₁ (anchoredBase base old η₁)) u.val) →
      (∀ u∈s,initialKeep η₂ (internalQ Q₂ (anchoredBase base old η₂)) u.val) →
      (∀ u∈s,rowNorm u ≤ Z) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (originalMark rayM Hr hHr old base θ W Z w σ v tOld) ≤
    C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
      (1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height))^degree*Z^(1+ε) := by
  obtain ⟨mesh,hm,hsource⟩ := native_pair_box hβ hy hy' hn hr hl0 hl ε hε
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs old base η₁ η₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d,S,C,hC,hsource⟩ := hsource Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ (anchoredBase base old η₁) (anchoredBase base old η₂) Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨B,hB,hbank⟩ := short_mark_bank rayM Hr hHr W hW.continuous hWs η₁ η₂
  refine ⟨d,S,B^(2*Fintype.card Slot)*C,by positivity,?_⟩
  filter_upwards [hsource,eventually_gt_atTop (1:ℝ)] with Z hsource hZ
  intro θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hv hsum
    p X₁ X₂ hX₁ hX₂ hXN hXY s hk₁ hk₂ hy
  exact physical_pair_all_at rayM Hr hHr hsource hB hbank θ w σ v tOld t₁ t₂ height
    hw hwm hσlo hσhi hh hv hsum hWs hZ p X₁ X₂ hX₁ hX₂ hXN hXY s hk₁ hk₂ hy

#print axioms native_original_pair_source
end
end QRH.Cycle092.StrongPair
