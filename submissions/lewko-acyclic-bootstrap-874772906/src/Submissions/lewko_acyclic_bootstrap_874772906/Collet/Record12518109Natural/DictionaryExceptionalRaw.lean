/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed finite dictionaries and all surviving original slot subsets share one
absolute constant for the exceptional physical branch. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.LabeledExceptionalRaw

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open Record12518109GainWholeGeometry WeightedHigh
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_dictionary_finite_core_raw_maximum
    {Index : Type}[Fintype Index](base : Index→Character)(η₀ : Character)
    (W : ℝ→ℂ)(lo hi : ℝ)(hWs : Function.support W⊆Icc (1:ℝ) 2)(hW : Continuous W) :
    ∃C : ℝ,0<C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀index : Index,
      ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
    Set.InjOn row (↑rows:Set Row) →∀(slots : Finset Slot)(w σ v : Slot→ℝ)
      (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
    (∀h∈rows,rawFrequencyNorm (row h)≤Z^Q) →
    (∀h∈rows,(wholeRegularDictionary M H hH (base index) η₀).exceptionalCore (sixthFrequencyEquiv.symm (row h)).1) →
    (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
      (excluded (naturalRow (base index) (row h).val (row h).property).character (mask h)) K) →
    (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
    (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
      C*Z^(Q/6+∑s∈slots,w s) := by
  let E:=fun index=>(wholeRegularDictionary M H hH (base index) η₀).exceptional_cores_finite.toFinset
  choose C hC hb using fun index=>actual_labeled_finite_core_raw_maximum (Slot:=Slot) M H hH (E index) W lo hi hWs hW
  let K:=fun index=>(E index).card*128*C index^(Fintype.card Slot)
  let Call : ℝ:=1+∑index,K index
  have hK (index : Index) : 0≤K index:=by
    have hc : 0≤C index:=by linarith [hC index]
    dsimp only [K]
    positivity
  have hCall : 0<Call:=by
    dsimp only [Call]
    have hh:=Finset.sum_nonneg (fun index (_ : index∈Finset.univ)=>hK index)
    linarith
  refine ⟨Call,hCall,?_⟩
  intro Z Q hZ hQ index Row _ rows row hinj slots w σ v t θ mask χ hnorm hex hcoeff hw hlo hhi
  have hh:=hb index Z Q hZ hQ (base index) η₀ rows row hinj slots w σ v t θ mask χ
    (fun h hh=>⟨hnorm h hh,(Set.Finite.mem_toFinset _).mpr (hex h hh)⟩) hcoeff hw hlo hhi
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  have hc : ((E index).card:ℝ)*128*C index^slots.card≤K index:=by
    apply mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (hC index) (Finset.card_le_univ slots))
      (by positivity)
  have hsum : K index≤∑j,K j:=Finset.single_le_sum (fun j _=>hK j) (Finset.mem_univ index)
  exact hc.trans (by dsimp only [Call];linarith)

theorem actual_uniform_labeled_tiny_raw_maximum
    (W : ℝ→ℂ)(lo hi : ℝ)(hWs : Function.support W⊆Icc (1:ℝ) 2)(hW : Continuous W) :
    ∃C : ℝ,0<C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀(ηchar η₀ : Character)
      {Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
    Set.InjOn row (↑rows:Set Row) →∀(slots : Finset Slot)(w σ v : Slot→ℝ)
      (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
    (∀h∈rows,rawFrequencyNorm (row h)≤Z^Q) →
    (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
      (excluded (naturalRow ηchar (row h).val (row h).property).character (mask h)) K) →
    (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
    (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
      C*Z^(Q+∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_labeled_tiny_raw_maximum (Slot:=Slot) M H hH W lo hi hWs hW
  refine ⟨128*C^(Fintype.card Slot),by positivity,?_⟩
  intro Z Q hZ hQ ηchar η₀ Row _ rows row hinj slots w σ v t θ mask χ hnorm hcoeff hw hlo hhi
  apply (hb Z Q hZ hQ ηchar η₀ rows row hinj slots w σ v t θ mask χ hnorm hcoeff hw hlo hhi).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (Finset.card_le_univ slots)) (by norm_num)

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_dictionary_finite_core_raw_maximum
#print axioms OAI.SevenEighths.Record12518109Natural.actual_uniform_labeled_tiny_raw_maximum
