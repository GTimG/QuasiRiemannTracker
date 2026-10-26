/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.AbsoluteSlots
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ExceptionalCounts
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualRootOrdinary

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109GainExceptional
noncomputable section
open scoped Classical BigOperators
open CenteredMomentNaturalRowSource
open HeckeFiniteDeletion
open LocalMoment HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ConcretePrimeRowBridge CenteredMomentCommonMaskExpansion CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot HeckePrimeAnnular HeckePrimeRay
open Record12518109GainWholeGeometry
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

/-- Original physical slots and original natural puncture, before root cleaning. -/
def originalNaturalSlotMaximum (η η₀ : Character) (W : ℝ→ℂ) (Z : ℝ)
    (slots : Finset Slot)(w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)
    (t : NonzeroFrequency→ℝ)(mask : NonzeroFrequency→Ideal O)(h : NonzeroFrequency) : ℝ :=
  ∏s∈slots,max 1 (‖naturalSlot (excluded (naturalRow η h.val h.property).character (mask h))
    (primePool M H 2 (Z^(w s)))
    (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
      annularWeight W (Z^(w s)) (σ s) (t h+v s) K) (Z^(w s))‖^2)

theorem actual_original_maximum_uniform (W : ℝ→ℂ) (lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z : ℝ),1≤Z →∀(η η₀ : Character)
      (slots : Finset Slot)(w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)
      (t : NonzeroFrequency→ℝ)(mask : NonzeroFrequency→Ideal O),
      (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      ∀h,originalNaturalSlotMaximum M H hH η η₀ W Z slots w σ v θ t mask h
        ≤C^slots.card*Z^(∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_original_slot_absolute (Slot:=Slot) M H hH W lo hi hWs hW
  refine ⟨C,hC,?_⟩
  intro Z hZ η η₀ slots w σ v θ t mask hw hlo hhi h
  exact hb Z hZ _ η₀ slots w σ v (t h) θ hw hlo hhi

/-- Actual fixed-inducing cost Q/6+L. No principal character or unit is omitted. -/
theorem actual_finite_core_raw_maximum (E : Finset FreeRow)
    (W : ℝ→ℂ) (lo hi : ℝ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀(η η₀ : Character)
      (slots : Finset Slot)(w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)
      (t : NonzeroFrequency→ℝ)(mask : NonzeroFrequency→Ideal O),
      (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      ∀rows : Finset NonzeroFrequency,
      (∀h∈rows,rawFrequencyNorm h≤Z^Q ∧(sixthFrequencyEquiv.symm h).1∈E) →
      (∑h∈rows,originalNaturalSlotMaximum M H hH η η₀ W Z slots w σ v θ t mask h)
        ≤((E.card:ℝ)*128*C^slots.card)*Z^(Q/6+∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_original_maximum_uniform (Slot:=Slot) M H hH W lo hi hWs hW
  refine ⟨C,hC,?_⟩
  intro Z Q hZ hQ η η₀ slots w σ v θ t mask hw hlo hhi rows hrows
  have hc:=finite_core_raw_count E (Z^Q) (Real.one_le_rpow hZ hQ) rows hrows
  calc
    _≤∑h∈rows,C^slots.card*Z^(∑s∈slots,w s) := Finset.sum_le_sum (fun h _=>hb Z hZ η η₀ slots w σ v θ t mask hw hlo hhi h)
    _=(rows.card:ℝ)*(C^slots.card*Z^(∑s∈slots,w s)) := by simp
    _≤((E.card:ℝ)*128*(Z^Q)^(1/6:ℝ))*(C^slots.card*Z^(∑s∈slots,w s)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by
      rw [←Real.rpow_mul (zero_le_one.trans hZ),show Q*(1/6:ℝ)=Q/6 by ring]
      rw [Real.rpow_add (zero_lt_one.trans_le hZ)]
      ring

/-- Actual unrestricted tiny-radius cost Q+L, uniform down to Q=0. -/
theorem actual_tiny_raw_maximum (W : ℝ→ℂ) (lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀(η η₀ : Character)
      (slots : Finset Slot)(w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)
      (t : NonzeroFrequency→ℝ)(mask : NonzeroFrequency→Ideal O),
      (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      ∀rows : Finset NonzeroFrequency,(∀h∈rows,rawFrequencyNorm h≤Z^Q) →
      (∑h∈rows,originalNaturalSlotMaximum M H hH η η₀ W Z slots w σ v θ t mask h)
        ≤(128*C^slots.card)*Z^(Q+∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_original_maximum_uniform (Slot:=Slot) M H hH W lo hi hWs hW
  refine ⟨C,hC,?_⟩
  intro Z Q hZ hQ η η₀ slots w σ v θ t mask hw hlo hhi rows hrows
  have hc:=all_raw_count (Z^Q) (Real.one_le_rpow hZ hQ) rows hrows
  calc
    _≤∑h∈rows,C^slots.card*Z^(∑s∈slots,w s) := Finset.sum_le_sum (fun h _=>hb Z hZ η η₀ slots w σ v θ t mask hw hlo hhi h)
    _=(rows.card:ℝ)*(C^slots.card*Z^(∑s∈slots,w s)) := by simp
    _≤(128*Z^Q)*(C^slots.card*Z^(∑s∈slots,w s)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [Real.rpow_add (zero_lt_one.trans_le hZ)];ring

theorem actual_fixed_inducing_raw_maximum {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label)
    (W : ℝ→ℂ) (lo hi : ℝ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z Q : ℝ),1≤Z →0≤Q →∀(η η₀ : Character)
      (slots : Finset Slot)(w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)
      (t : NonzeroFrequency→ℝ)(mask : NonzeroFrequency→Ideal O),
      (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      ∀rows : Finset NonzeroFrequency,
      (∀h∈rows,rawFrequencyNorm h≤Z^Q) →
      (∑h∈rows.filter (fun h=>D.exceptionalCore (sixthFrequencyEquiv.symm h).1),originalNaturalSlotMaximum M H hH η η₀ W Z slots w σ v θ t mask h)
        ≤((D.exceptional_cores_finite.toFinset.card:ℝ)*128*C^slots.card)*Z^(Q/6+∑s∈slots,w s) := by
  obtain ⟨C,hC,hb⟩:=actual_finite_core_raw_maximum (Slot:=Slot) M H hH
    D.exceptional_cores_finite.toFinset W lo hi hWs hW
  refine ⟨C,hC,?_⟩
  intro Z Q hZ hQ η η₀ slots w σ v θ t mask hw hlo hhi rows hrows
  apply hb Z Q hZ hQ η η₀ slots w σ v θ t mask hw hlo hhi
  intro h hh
  obtain ⟨hh,hex⟩:=Finset.mem_filter.mp hh
  exact ⟨hrows h hh,(Set.Finite.mem_toFinset _).mpr hex⟩

end
end OAI.SevenEighths.Record12518109GainExceptional
