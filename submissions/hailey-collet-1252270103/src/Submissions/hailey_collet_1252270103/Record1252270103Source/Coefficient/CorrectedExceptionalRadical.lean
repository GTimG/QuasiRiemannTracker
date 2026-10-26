/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed-character exceptional sixth-root count supplies two radical powers
before the squarefree ordinary allocation moments are paid.  In particular the
(2,2) common type is not relaxed to a full common-norm centered moment. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
noncomputable section
open scoped Classical BigOperators
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentCanonicalFirst
open CenteredMomentPartitionNorm CenteredMomentForcing CenteredMomentSecondPhysicalLedger
local notation "O" => ActualEisensteinCubic.O

/-- The forcing count pays the borderline (1,1) nonunit case exactly.
No restriction on the two positive valuations is needed. -/
theorem local_radical_saving (c d : ℕ) (hc : 1≤c) (hd : 1≤d) (nonunit : Prop) :
    1≤localSaving c d nonunit+(if c=d ∧ c=1 ∧ nonunit then (1/3:ℝ) else 0) := by
  have hmc : (min c d:ℝ)≤c := min_le_left _ _
  have hmd : (min c d:ℝ)≤d := min_le_right _ _
  by_cases hc1 : c=1
  · subst c
    by_cases hd1 : d=1
    · subst d
      by_cases hn : nonunit <;> norm_num [localSaving,hn]
    · have hd2 : (2:ℝ)≤d := by exact_mod_cast (show 2≤d by omega)
      have hne : ¬(1:ℕ)=d := by omega
      simp only [localSaving,hne,false_and,ite_false,add_zero,Nat.cast_one,
        min_eq_left (by exact_mod_cast hd : (1:ℝ)≤d)]
      linarith
  · by_cases hd1 : d=1
    · subst d
      have hc2 : (2:ℝ)≤c := by exact_mod_cast (show 2≤c by omega)
      simp only [localSaving,hc1,false_and,ite_false,add_zero,Nat.cast_one,
        min_eq_right (by exact_mod_cast hc : (1:ℝ)≤c)]
      linarith
    · have hc2 : (2:ℝ)≤c := by exact_mod_cast (show 2≤c by omega)
      have hd2 : (2:ℝ)≤d := by exact_mod_cast (show 2≤d by omega)
      unfold localSaving
      split_ifs <;> linarith

theorem secondSaving_radical (ι : Type*) [Fintype ι] [DecidableEq ι]
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (c d : ι→ℕ) (hc : ∀i,1≤c i) (hd : ∀i,1≤d i)
    (w : O) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (Ideal.absNorm (∏i,Ideal.span {p i}):ℝ)≤
      secondSaving p c d w Z+
        Real.logb Z (Ideal.absNorm (forcingIdeal (fun i=>Ideal.span {p i})
          c d (actualNonunitSet p c d w)):ℝ)/3 := by
  rw [log_norm_radical p hp Finset.univ]
  unfold forcingIdeal
  rw [log_norm_radical p hp]
  simp only [forcingSet,actualNonunitSet,Finset.filter_filter,Finset.sum_filter,
    Finset.sum_div,secondSaving,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hf : ((c i=d i ∧ ¬6∣c i ∧ p i∣CenteredMomentPartition.dividedFrequency p c d w i) ∧
      c i=1 ∧ d i=1) ↔
      (c i=d i ∧ c i=1 ∧ p i∣CenteredMomentPartition.dividedFrequency p c d w i) := by
    constructor
    · rintro ⟨⟨hcd,h6,hn⟩,hc1,hd1⟩
      exact ⟨hcd,hc1,hn⟩
    · rintro ⟨hcd,hc1,hn⟩
      exact ⟨⟨hcd,by omega,hn⟩,hc1,by omega⟩
  simp only [hf]
  have hn : 0≤Real.logb Z (Ideal.absNorm (Ideal.span {p i}):ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
  have hh:=mul_le_mul_of_nonneg_left
    (local_radical_saving (c i) (d i) (hc i) (hd i)
      (p i∣CenteredMomentPartition.dividedFrequency p c d w i)) hn
  split_ifs at hh ⊢ <;> linarith

/-- The literal canonical partition, including its forcing ideal, has enough
arithmetic decay to pay a squarefree ordinary radical on each side. -/
theorem actual_radical_log_saving (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (w : O) (hpart : canonicalPartition C D U w) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)≤
      saving C D U Z+Real.logb Z (forcingNorm C D U)/3 := by
  have hh:=secondSaving_radical (CommonIndex C D) (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) w Z hZ
  rw [secondSaving_eq_norm_ledger _ (commonPrime_supported C D hC)] at hh
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD,
    ←commonFrequencyGenerator_span C D hC] at hh
  change actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U at hpart
  rw [hpart,←nonunitPartitionSet_eq_actual C D U w hpart,
    ←nonunitFrequencyGenerator_span C D U] at hh
  simpa only [saving,forcingNorm,unitIdeal,commonPrime_span C D hC,forcingIdeal] using hh

/-- Positive scalar form of the prime ledger, with the full Fourier-frequency
and forcing powers. -/
theorem radical_scalar_bound (Z c d g u v f r : ℝ)
    (hZ : 1<Z) (hc : 0<c) (hd : 0<d) (hg : 0<g) (hu : 0<u)
    (hv : 0<v) (hf : 0<f) (hr : 0<r)
    (hledger : 2*Real.logb Z r≤Real.logb Z c+Real.logb Z d-
      5*Real.logb Z g/6+Real.logb Z u+Real.logb Z v/6+2*Real.logb Z f/3) :
    (g/u)/(c*d*(g*v)^(1/6:ℝ)*f^(2/3:ℝ))≤r^(-2:ℝ) := by
  apply (Real.logb_le_logb hZ (show 0<(g/u)/(c*d*(g*v)^(1/6:ℝ)*f^(2/3:ℝ)) by positivity)
    (Real.rpow_pos_of_pos hr _)).mp
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos (mul_pos hg hv),
    Real.logb_rpow_eq_mul_logb_of_pos hf,Real.logb_rpow_eq_mul_logb_of_pos hr]
  linarith

theorem actual_radical_scalar_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (w : O) (hpart : canonicalPartition C D U w) (Z : ℝ) (hZ : 1<Z) :
    CenteredMomentSecondCanonicalScalar.normalizer C D U/
      ((C.absNorm:ℝ)*(D.absNorm:ℝ)*
        (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}):ℝ)^(1/6:ℝ)*
        (forcingNorm C D U)^(2/3:ℝ))≤
      (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(-2:ℝ) := by
  have hc : (0:ℝ)<C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd : (0:ℝ)<D.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg : (0:ℝ)<Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hv : (0:ℝ)<Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hr:=common_product_pos C D hC Finset.univ
  have hf : 0<forcingNorm C D U:=common_product_pos C D hC _
  have hs:=actual_radical_log_saving C D hC hD hCD U w hpart Z hZ
  unfold saving at hs
  have he := radical_scalar_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)
    (Ideal.absNorm (∏P∈U,P.val):ℝ)
    (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)
    (forcingNorm C D U) (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)
    hZ hc hd hg hu hv hf hr (by linarith)
  rw [CenteredMomentSecondCanonicalScalar.normalizer,actual_partitionNormalizer C D hC,
    ←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]
  exact he

end
end OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.local_radical_saving
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.secondSaving_radical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_radical_log_saving
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.radical_scalar_bound
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_radical_scalar_bound
