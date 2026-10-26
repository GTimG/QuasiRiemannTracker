/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal finite inducing-core and tiny-radius suppliers pulled back along the
actual injective row map. No zero, witness or energy estimate is assumed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.LabeledRegularRawTau

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot HeckePrimeAnnular Cycle61Moment
open Record12518109GainWholeGeometry Record12518109GainExceptional Record12518109Gain WeightedHigh
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

lemma actual_labeled_slot_maximum_pullback
    (ηchar η₀ : Character)(W : ℝ→ℂ)(Z : ℝ)(hZ : 0<Z)
    {Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency)
    (hinj : Set.InjOn row (↑rows:Set Row))(slots : Finset Slot)(w σ v : Slot→ℝ)
    (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character)
    (hcoeff : ∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
      (excluded (naturalRow ηchar (row h).val (row h).property).character (mask h)) K) :
    (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)=
    ∑u∈rows.image row,originalNaturalSlotMaximum M H hH ηchar η₀ W Z slots w σ v θ
      (fun u=>t (FiniteRows.pullback rows row u)) (fun u=>mask (FiniteRows.pullback rows row u)) u := by
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro l hl
  dsimp only [originalNaturalSlotMaximum]
  simp only [FiniteRows.pullback_row rows row hinj hl]
  rw [←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro s hs
  rw [maximum_square _ (norm_nonneg _)]
  congr 2
  unfold labeledRawSlot
  rw [natural_annular_slot_norm _ _ _ _ (fun K hK=>(Finset.mem_filter.mp hK).2.1.ne_zero)
    _ _ _ _ (Real.rpow_pos_of_pos hZ _)]
  congr 1
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro K _
  rw [hcoeff l hl K]

theorem actual_labeled_finite_core_raw_maximum (E : Finset FreeRow)
    (W : ℝ→ℂ)(lo hi : ℝ)(hWs : Function.support W⊆Icc (1:ℝ) 2)(hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀(ηchar η₀ : Character)
      {Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
    Set.InjOn row (↑rows:Set Row) →∀(slots : Finset Slot)(w σ v : Slot→ℝ)
      (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
    (∀h∈rows,rawFrequencyNorm (row h)≤Z^Q ∧(sixthFrequencyEquiv.symm (row h)).1∈E) →
    (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
      (excluded (naturalRow ηchar (row h).val (row h).property).character (mask h)) K) →
    (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
    (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
      ((E.card:ℝ)*128*C^slots.card)*Z^(Q/6+∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_finite_core_raw_maximum (Slot:=Slot) M H hH E W lo hi hWs hW
  refine ⟨C,hC,?_⟩
  intro Z Q hZ hQ ηchar η₀ Row _ rows row hinj slots w σ v t θ mask χ hnorm hcoeff hw hlo hhi
  rw [actual_labeled_slot_maximum_pullback M H hH ηchar η₀ W Z (zero_lt_one.trans_le hZ)
    rows row hinj slots w σ v t θ mask χ hcoeff]
  apply hb Z Q hZ hQ ηchar η₀ slots w σ v θ _ _ hw hlo hhi
  intro u hu
  obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hu
  exact hnorm l hl

theorem actual_labeled_tiny_raw_maximum
    (W : ℝ→ℂ)(lo hi : ℝ)(hWs : Function.support W⊆Icc (1:ℝ) 2)(hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀(ηchar η₀ : Character)
      {Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
    Set.InjOn row (↑rows:Set Row) →∀(slots : Finset Slot)(w σ v : Slot→ℝ)
      (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
    (∀h∈rows,rawFrequencyNorm (row h)≤Z^Q) →
    (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
      (excluded (naturalRow ηchar (row h).val (row h).property).character (mask h)) K) →
    (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
    (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
      (128*C^slots.card)*Z^(Q+∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_tiny_raw_maximum (Slot:=Slot) M H hH W lo hi hWs hW
  refine ⟨C,hC,?_⟩
  intro Z Q hZ hQ ηchar η₀ Row _ rows row hinj slots w σ v t θ mask χ hnorm hcoeff hw hlo hhi
  rw [actual_labeled_slot_maximum_pullback M H hH ηchar η₀ W Z (zero_lt_one.trans_le hZ)
    rows row hinj slots w σ v t θ mask χ hcoeff]
  apply hb Z Q hZ hQ ηchar η₀ slots w σ v θ _ _ hw hlo hhi
  intro u hu
  obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hu
  exact hnorm l hl

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_labeled_finite_core_raw_maximum
#print axioms OAI.SevenEighths.Record12518109Natural.actual_labeled_tiny_raw_maximum
