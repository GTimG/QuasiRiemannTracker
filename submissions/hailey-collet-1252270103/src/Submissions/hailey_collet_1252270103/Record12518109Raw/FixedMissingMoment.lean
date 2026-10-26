/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.FixedMissingSelection
import Submissions.hailey_collet_1252270103.Record12518109Raw.InjectiveMoment

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentEnergySlotHeight
open CenteredMomentEnergyProfiles CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

/-- Regroup the complete weighted normalized RAW product at one fixed missing
radical. The actual row retains its unit, first numerator, second common and
nonunit generators, and retained sixth power. Only encoding multiplicity is
paid here; the missing radical is fixed and is not summed a second time. -/
theorem actual_fixed_missing_weighted_raw_moment {α : Type*} [DecidableEq α]
    (F : Finset α) (bslot Mslot : α → ℝ) (hM : ∀ j ∈ F, 0 ≤ Mslot j)
    (B loss ε : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
      (Z : ℝ), 2 ≤ Z → ∀ H : Ideal O, H ≠ 0 →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀ l ∈ labels, ((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((Ideal.span {(nonzeroJointSourceRow l).val} * H).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, ps l.val.1.1.1 = ps l.val.1.1.2 ∧ ps l.val.2.1.1 = ps l.val.2.1.2) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, firstSourceMissing left l.val.1 = H) →
      ∀ (η : Character) (Q R : Ideal O), R ≠ 0 →
      (∀ l : labels, initialKeep η Q (nonzeroJointSourceRow l.val).val) →
      ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ), 0 ≤ b →
      Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b →
      ∀ (pool : α → Finset (Ideal O)) (ν : α → Character)
        (Wslot : α → ℝ → ℂ) (P σ freq : α → ℝ) (t : ℝ),
      (∀ j ∈ F, ∀ I ∈ pool j, Prime I) → (∀ j ∈ F, 0 < P j) →
      (∀ j ∈ F, ∀ I ∈ pool j,
        ‖idealCoeff (ν j) I * HeckePrimeAnnular.annularWeight (Wslot j) (P j) (σ j) (freq j) I‖ ≤ Mslot j) →
      (∀ j ∈ F, ∀ I ∈ pool j,
        idealCoeff (ν j) I * HeckePrimeAnnular.annularWeight (Wslot j) (P j) (σ j) (freq j) I ≠ 0 →
        (I.absNorm : ℝ) ≤ bslot j * P j) →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (K E lo hi low high A : ℝ)
        (lx ly weight : labels → ℝ),
      0 < K → (∀ x, 0 ≤ (Φ x).re) →
      (∀ l : labels, 1 ≤ (Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2 / K)).re) →
      0 ≤ E → lo ≤ hi → low ≤ high →
      (∀ l, lx l ∈ Set.Icc lo hi) → (∀ l, ly l ∈ Set.Icc low high) →
      0 ≤ A → (∀ l, 0 ≤ weight l) → (∀ l, weight l ≤ A) →
      (∀ D₁ ∈ (ps (R*H)).powerset, ∀ D₂ ∈ (ps (R*H)).powerset, ∀ J ∈ F.powerset,
        ∀ j k : Fin 2,
        ∀ x ∈ Set.Icc (lo-Real.log ((∏ I ∈ D₁,I).absNorm : ℝ))
          (hi-Real.log ((∏ I ∈ D₁,I).absNorm : ℝ)),
        ∀ y ∈ Set.Icc (low-Real.log ((∏ I ∈ D₂,I).absNorm : ℝ))
          (high-Real.log ((∏ I ∈ D₂,I).absNorm : ℝ)),
        energy η (fixedBadMask*idealGenerator 1) 1 0
          (derivativeChoice W₁ j) (derivativeChoice W₂ k)
          (fun i : ↥(F \ J) => pool i)
          (fun (i : ↥(F \ J)) I => idealCoeff (ν i) I *
            HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t+freq i) I)
          (fun i : ↥(F \ J) => P i) (Real.exp x) (Real.exp y) (initialKeep η Q) Φ K ≤ E) →
      let N := fun l : labels => naturalRow η (nonzeroJointSourceRow l.val).val
        (nonzeroJointSourceRow l.val).property
      (∑ l : labels, weight l * ‖polynomial (excluded (N l).character (R*H)) false W₁ (Real.exp (lx l)) 0 0 *
        polynomial (excluded (N l).character (R*H)) false W₂ (Real.exp (ly l)) 0 0 *
        ∏ i ∈ F, naturalSlot (excluded (N l).character (R*H)) (pool i)
          (heightCoefficient (fun I => idealCoeff (ν i) I *
            HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i)‖^2) ≤
      C * Z^loss * A * ((∏ I ∈ ps (R*H), I).absNorm : ℝ)^ε *
        ((1+2*(hi-lo))*((1+2*(high-low))*E)) := by
  obtain ⟨Cf,hCf,hfiber⟩ := actual_fixed_missing_row_selection B loss hB hloss
  obtain ⟨Cm,hCm,hmoment⟩ := canonical_masked_injective_rowwise_from_energy F bslot Mslot hM ε hε
  refine ⟨Cf*Cm,mul_pos hCf hCm,?_⟩
  intro left u₀ unit Z hZ H hH labels hrow hsupport hn heq hnorm hmissing
    η Q R hR hkeep W₁ W₂ a b hb hs₁ hs₂ pool ν Wslot P σ freq t hp hP hβ hslot
    Φ K E lo hi low high A lx ly weight hK hΦ hcover hE hlo hlow hlx hly hA hw hwA hsource N
  let value := fun l : labels =>
    polynomial (excluded (N l).character (R*H)) false W₁ (Real.exp (lx l)) 0 0 *
    polynomial (excluded (N l).character (R*H)) false W₂ (Real.exp (ly l)) 0 0 *
    ∏ i ∈ F, naturalSlot (excluded (N l).character (R*H)) (pool i)
      (heightCoefficient (fun I => idealCoeff (ν i) I *
        HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i)
  let cost := fun l => weight l * ‖value l‖^2
  obtain ⟨pick,hpick,hinj,hbound⟩ := hfiber left u₀ unit Z hZ H hH labels
    hrow hsupport hn heq hnorm hmissing cost (fun l => mul_nonneg (hw l) (sq_nonneg _))
  let row := fun l : labels => nonzeroJointSourceRow l.val
  let ι := ↥(Finset.univ.image row)
  have hactual : Function.Injective (fun w : ι => (row (pick w)).val) := by
    intro w v he
    exact hinj (Subtype.ext he)
  have hm := hmoment η Q (R*H) (mul_ne_zero hR hH) W₁ W₂ a b hb hs₁ hs₂
    pool ν Wslot P σ freq t hp hP hβ hslot ι
    (fun w => (row (pick w)).val) hactual (fun w => hkeep (pick w))
    (fun w => N (pick w)) Φ K E lo hi low high (fun w => lx (pick w)) (fun w => ly (pick w))
    hK hΦ (fun w => hcover (pick w)) hE hlo hlow
    (fun w => hlx (pick w)) (fun w => hly (pick w)) hsource
  have hs : (∑ w : ι, cost (pick w)) ≤ A * ∑ w : ι, ‖value (pick w)‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_right (hwA (pick w)) (sq_nonneg _))
  have hm' : (∑ w : ι, ‖value (pick w)‖^2) ≤
      Cm * ((∏ I ∈ ps (R*H), I).absNorm : ℝ)^ε *
        ((1+2*(hi-lo))*((1+2*(high-low))*E)) := hm
  apply hbound.trans
  apply (mul_le_mul_of_nonneg_left
    (hs.trans (mul_le_mul_of_nonneg_left hm' hA))
    (mul_nonneg hCf.le (Real.rpow_nonneg (by linarith) _))).trans_eq
  ring

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.actual_fixed_missing_weighted_raw_moment
