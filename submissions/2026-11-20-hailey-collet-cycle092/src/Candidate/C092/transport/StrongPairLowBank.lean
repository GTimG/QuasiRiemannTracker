/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The true independent-pair finite radius bank: earlier caps below the source
seam and genuine native mean fourths above it, with one fixed metadata set. -/
import Candidate.C092.transport.StrongPairLowNative
import Candidate.C092.transport.LowActualBankPayment

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
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.LowActual QRH.Cycle092.Source
local notation "O" => ActualEisensteinCubic.O

theorem pair_radius_bank_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y r : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hr0 : (98/100:ℝ) ≤ r) (hr1 : r ≤ (H:ℝ)) :
    ∀ l : ℝ,0 ≤ l → l < radiusWidth n y r → PairUniformBox (n/r) (y/r) l := by
  have hr : 0 < r := (by norm_num : (0:ℝ) < 98/100).trans_le hr0
  by_cases hseam : y/r ≤ sourceY
  · have hsource := earlier_low_pair cover (source_domain.1.le.trans hy0) hn0 hn1 hr hr1 hseam
    simpa [radiusWidth,continuedGain,hseam,sourceWidth,PairOpenWidth] using hsource
  · intro l hl0 hl
    have hN : n/r < 1/2 := by
      apply (div_lt_iff₀ hr).2
      norm_num [sourceY,sourceRatio] at hy1 hn1
      nlinarith
    have hY : y/r < 1/2 := by
      apply (div_lt_iff₀ hr).2
      norm_num [sourceY] at hy1
      nlinarith
    have hypos : 0 ≤ y := source_domain.1.le.trans hy0
    have hrle : r ≤ 1 := hr1.trans H_real_bounds.2.le
    have hyr : y ≤ y/r := (le_div_iff₀ hr).2 (mul_le_of_le_one_right hypos hrle)
    have hnr : y ≤ n/r := hyr.trans (div_le_div_of_nonneg_right hn0 hr.le)
    have hYlo : (7/20:ℝ) ≤ y/r := by norm_num [sourceY0] at hy0; linarith
    have hNlo : (7/20:ℝ) ≤ n/r := by norm_num [sourceY0] at hy0; linarith
    have hmean : l < (1-n/r-y/r)/2 := by simpa [radiusWidth,continuedGain,hseam] using hl
    exact native_mean_pair_box hβ hNlo hYlo hN hY hl0 hmean

/-- All metadata are fixed for the whole finite bank before the live radius,
its bank choice, the ordinary profiles, amplitudes, mark arrays and rows. -/
theorem pair_finite_bank_metadata {Index : Type*} [DecidableEq Index]
    (bank : Finset Index) (N Y l : Index→ℝ) {mesh ε Vmin : ℝ}
    (hsource : ∀ i∈bank,PairUnitBox (N i) (Y i) (l i) mesh ε) (hVmin : 0 < Vmin)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (hΦs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (hQ₁ray : Q₁ ≤ rayM) (hQ₁0 : internalQ Q₁ η₀₁ ≠ 0) (hQ₁top : internalQ Q₁ η₀₁ ≠ ⊤)
    (hQ₁72 : internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)})
    (hQ₂ray : Q₂ ≤ rayM) (hQ₂0 : internalQ Q₂ η₀₂ ≠ 0) (hQ₂top : internalQ Q₂ η₀₂ ≠ ⊤)
    (hQ₂72 : internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ,∃ S : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,Vmin ≤ V →∀ i∈bank,
      PairAt (Slot:=Slot) rayM Hr hHr (N i) (Y i) (l i) W bΦ mesh ε (U^V)
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ d S C := by
  induction bank using Finset.induction_on with
  | empty => exact ⟨0,∅,1,by norm_num,Filter.Eventually.of_forall (by simp)⟩
  | insert i bank hi ih =>
    obtain ⟨di,Si,Ci,hCi,hiU⟩ := pair_radius_metadata (hsource i (Finset.mem_insert_self _ _)) hVmin
      Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
      hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
    obtain ⟨db,Sb,Cb,hCb,hbU⟩ := ih (fun j hj=>hsource j (Finset.mem_insert_of_mem hj))
    refine ⟨max di db,Si∪Sb,Ci+Cb,add_pos hCi hCb,?_⟩
    filter_upwards [hiU,hbU,eventually_ge_atTop (1:ℝ)] with U hiU hbU hU
    intro V hV j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact pairAt_metadata_mono rayM Hr hHr (Real.rpow_nonneg (zero_le_one.trans hU) _) hCi.le
        (by linarith) (le_max_left _ _) Finset.subset_union_left (hiU V hV)
    · exact pairAt_metadata_mono rayM Hr hHr (Real.rpow_nonneg (zero_le_one.trans hU) _) hCb.le
        (by linarith) (le_max_right _ _) Finset.subset_union_right (hbU V hV j hj)

#print axioms pair_radius_bank_source
#print axioms pair_finite_bank_metadata
end
end QRH.Cycle092.StrongPair
