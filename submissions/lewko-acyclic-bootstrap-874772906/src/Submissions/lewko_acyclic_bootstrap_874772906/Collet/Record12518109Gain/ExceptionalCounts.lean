/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.RootCompletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawCompact

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109GainExceptional
noncomputable section
open scoped Classical BigOperators
open LocalMoment HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ConcretePrimeRowBridge Record12518109GainRoot
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

lemma sixth_fiber_raw_mem (R : Finset NonzeroFrequency) (B : NZIdeal)
    (u : FreeRow) (hu : u∈sixthFreeFiber R B) : sixthFrequencyEquiv (u,B)∈R := by
  obtain ⟨p,hp,hpu⟩:=Finset.mem_image.mp hu
  obtain ⟨hp,hpB⟩:=Finset.mem_filter.mp hp
  have he : p=(u,B):=Prod.ext hpu hpB
  subst p
  exact (mem_sixthPairs R (u,B)).mp hp

/-- All six units are contained in the actual free-core population E. -/
theorem finite_core_raw_count (E : Finset FreeRow) (H : ℝ) (hH : 1≤H)
    (R : Finset NonzeroFrequency)
    (hR : ∀h∈R,rawFrequencyNorm h≤H ∧(sixthFrequencyEquiv.symm h).1∈E) :
    (R.card:ℝ)≤(E.card:ℝ)*128*H^(1/6:ℝ) := by
  let roots:=(sixthPairs R).image Prod.snd
  have hnorm (B : NZIdeal) (hB : B∈roots) : (B.val.absNorm:ℝ)≤H^(1/6:ℝ) := by
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hB
    have hr:=hR _ ((mem_sixthPairs R p).mp hp)
    rw [raw_sixth_norm] at hr
    have hb0 : 0≤(p.2.val.absNorm:ℝ):=Nat.cast_nonneg _
    have hpow : (p.2.val.absNorm:ℝ)^6≤H := by
      nlinarith [rowNorm_ge_one p.1, pow_nonneg hb0 6]
    simpa only [one_div] using
      (Real.le_rpow_inv_iff_of_pos hb0 (zero_le_one.trans hH) (by norm_num : (0:ℝ)<6)).mpr
        (by rw [show (6:ℝ)=((6:ℕ):ℝ) by norm_num,Real.rpow_natCast];exact hpow)
  have hcard : (roots.card:ℝ)≤128*H^(1/6:ℝ) := by
    by_cases hs : roots.Nonempty
    · obtain ⟨B,hB⟩:=hs
      have hb1 : 1≤(B.val.absNorm:ℝ):=by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
      have hc:=DescentFiberCost.finite_ideal_count_real (roots.image Subtype.val)
        (H^(1/6:ℝ)) (hb1.trans (hnorm B hB))
        (by intro I hI;obtain ⟨B,hB,rfl⟩:=Finset.mem_image.mp hI;exact B.property)
        (by intro I hI;obtain ⟨B,hB,rfl⟩:=Finset.mem_image.mp hI;exact hnorm B hB)
      rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hc
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.card_empty,Nat.cast_zero]
      positivity
  have hfiber (B : NZIdeal) : (sixthFreeFiber R B).card≤E.card := by
    apply Finset.card_le_card
    intro u hu
    have hr:=(hR _ (sixth_fiber_raw_mem R B u hu)).2
    simpa only [Equiv.symm_apply_apply] using hr
  rw [raw_sixth_cardinality,Nat.cast_sum]
  calc
    _≤∑B∈roots,(E.card:ℝ) := Finset.sum_le_sum (fun B _=>by exact_mod_cast hfiber B)
    _=(roots.card:ℝ)*(E.card:ℝ) := by simp
    _≤(128*H^(1/6:ℝ))*(E.card:ℝ) := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
    _=_ := by ring

theorem all_raw_count (H : ℝ) (hH : 1≤H) (R : Finset NonzeroFrequency)
    (hR : ∀h∈R,rawFrequencyNorm h≤H) : (R.card:ℝ)≤128*H := by
  exact DetectorDictionaryInverseRawCompact.nonzero_element_rows_card R H hH hR

end
end OAI.SevenEighths.Record12518109GainExceptional
