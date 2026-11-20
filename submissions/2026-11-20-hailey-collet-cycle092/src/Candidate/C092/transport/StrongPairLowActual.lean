/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual original-mark low source on the detector's fixed witness pairs.
Both independent ordinary anchors use the same original kept finite rows. -/
import Candidate.C092.transport.StrongPairLowNear
import Candidate.C092.transport.StrongPairLowWitness

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

/-- This contains no extra keep gate, no mark-presentation premise and no
assumed substituted-pair energy. Witness labels and original prime holes
remain exact even at bounded/zero slot width. -/
theorem low_original_witness_pairs {n y e Vmax : ℝ}
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
    ∀ (η base : Character)
      (j₁ j₂ : Option (RayQuotient.Characters rayM Hr × RayQuotient.Characters rayM Hr)) (Q : Ideal O),
      Q ≤ rayM → internalQ Q base ≠ 0 → internalQ Q base ≠ ⊤ → internalQ Q base ≤ Ideal.span {(72:O)} →
    ∀ Cslot : ℝ,0 ≤ Cslot →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
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
  obtain ⟨mesh,hm,hsource⟩ := low_pair_near_radii hmax hβ cover hy0 hy1 hn0 hn1 he0 he1 hp
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  obtain ⟨buffer,hb,hsource⟩ := hsource Slot
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η base j₁ j₂ Q hQray hQ0 hQtop hQ72 Cslot hCslot
  have hq₁ := witness_internalQ rayM Hr hHr Q hQray base j₁
  have hq₂ := witness_internalQ rayM Hr hHr Q hQray base j₂
  obtain ⟨degree,controls,C,hC,hsource⟩ := hsource rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    (witnessBase rayM Hr hHr η base j₁) (witnessBase rayM Hr hHr η base j₂)
    (witnessBase rayM Hr hHr base base j₁) (witnessBase rayM Hr hHr base base j₂) Q Q
    hQray (by simpa only [hq₁] using hQ0) (by simpa only [hq₁] using hQtop) (by simpa only [hq₁] using hQ72)
    hQray (by simpa only [hq₂] using hQ0) (by simpa only [hq₂] using hQtop) (by simpa only [hq₂] using hQ72)
    Cslot hCslot
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsource,eventually_gt_atTop (1:ℝ)] with U hsource hU
  intro V hVmin hVmax θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hv hwidth
    p X₁ X₂ hX₁ hX₂ hXN hXY s hk hy hlow
  have hv₁ : ∀ i,|tOld+v i-t₁| ≤ |tOld|+|t₁|+|t₂|+height := by
    intro i
    have h := abs_sub (tOld+v i) t₁
    have ha := abs_add_le tOld (v i)
    linarith [hv i,abs_nonneg t₂]
  have hv₂ : ∀ i,|tOld+v i-t₂| ≤ |tOld|+|t₁|+|t₂|+height := by
    intro i
    have h := abs_sub (tOld+v i) t₂
    have ha := abs_add_le tOld (v i)
    linarith [hv i,abs_nonneg t₁]
  apply hsource V hVmin hVmax θ θ w σ σ (fun i=>tOld+v i-t₁) (fun i=>tOld+v i-t₂)
    t₁ t₂ (|tOld|+|t₁|+|t₂|+height) hw hwm hσlo hσhi hσlo hσhi (by positivity)
    hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY s _
    (fun u hu=>(witness_initialKeep rayM Hr hHr Q hQray η base j₁ u).mpr (hk u hu))
    (fun u hu=>(witness_initialKeep rayM Hr hHr Q hQray η base j₂ u).mpr (hk u hu)) hy
  · intro u hu i
    exact (witness_original_mark_norm rayM Hr hHr η base j₁ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (originalPools rayM Hr 2 U w i) W
      (U^(w i)) (σ i) tOld t₁ (v i) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)).symm
  · intro u hu i
    exact (witness_original_mark_norm rayM Hr hHr η base j₂ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (originalPools rayM Hr 2 U w i) W
      (U^(w i)) (σ i) tOld t₂ (v i) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)).symm
  · exact hlow

#print axioms low_original_witness_pairs
end
end QRH.Cycle092.StrongPair
