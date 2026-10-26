/- Pure actual-label prefix bounds, including empty/direct/zero source branches.
Copyright (c)2026 Zhongpai Gao. Native factorization bounds by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.NativeChildPrefix
import Candidate.Cycle63.Physical.InitialMass.SecondRatioCap
import Candidate.Cycle63.Physical.InitialMass.SecondCoarseSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalFrequency IdealMobiusDivisorSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentFirstSourceConductorCaps Cycle63Moment Cycle63InitialMass

/-- Unit choice and the literal supported labels alone bound the successor
multiplier. No continued child, nonzero source row or energy is required. -/
theorem actual_label_child_norm_bound (Z : ℝ)(hZ : 1<Z)
    (left : Bool)(u0 : O)(units : FirstSourceLabel→O)(hu0 : u0≠0)
    (hunits : ∀l,IsUnit (units l))(p : Cycle63Moment.ChildPrefix)
    (hC1 : Supported p.1.1.1)(hD1 : Supported p.1.1.2)
    (hC2 : Supported p.2.1.1)(hD2 : Supported p.2.1.2)
    (hCD2 : primeSupport p.2.1.1=primeSupport p.2.1.2)
    (B1 B2 : ℝ)(hcap1 : (p.1.1.1.absNorm:ℝ) ≤ Z^B1)
    (hcap2 : (p.2.1.1.absNorm:ℝ) ≤ Z^B2) :
    childMultiplier left u0 units p≠0 ∧
      normValue (childMultiplier left u0 units p) ≤ normValue u0*Z^(6*B1+2*B2) :=by
  have hne : childMultiplier left u0 units p≠0 :=by
    have hS : primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2=>P.val) p.1.2.val≠0 :=
      Ideal.span_singleton_eq_bot.not.mp (subsetGenerator_supported _ _ hC1 p.1.2.val).1
    have hF:=first_source_numerator_ne_zero left p.1 hC1
    have hG:=commonFrequencyGenerator_ne_zero p.2.1.1 p.2.1.2 hC2
    have hV:=nonunitFrequencyGenerator_ne_zero p.2.1.1 p.2.1.2 hC2 p.2.2
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hu0 (hunits p.1).ne_zero) hS) hF)
      (mul_ne_zero hG hV)
  refine ⟨hne,?_⟩
  let S:=primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2=>P.val) p.1.2.val
  let F:=firstSourceNumerator left p.1
  let G:=commonFrequencyGenerator p.2.1.1 p.2.1.2*nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2
  have hS : normValue S ≤ Z^B1 :=by
    apply le_trans ?_ hcap1
    exact divisor_norm_le _ p.1.1.1 hC1.1
      ((subsetGenerator_span_dvd p.1.1.1 p.1.1.2 p.1.2.val).trans (commonPart_dvd _ _ hC1.1))
  have hFne : F≠0:=first_source_numerator_ne_zero left p.1 hC1
  have hF : normValue F ≤ Z^(5*B1) :=by
    apply (Real.logb_le_iff_le_rpow hZ (normValue_pos _ hFne)).mp
    have hfirst:=first_numerator_log_le left p.1 hC1 hD1 Z hZ
    have hCpos : (0:ℝ)<(p.1.1.1.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC1.1)
    have hClog:=(Real.logb_le_iff_le_rpow hZ hCpos).mpr hcap1
    dsimp only [F]
    linarith only [hfirst,hClog]
  have hG : normValue G ≤ Z^(2*B2) :=by
    have hf:=(actual_second_frequency_norm_cap _ _ hC2 hD2 hCD2 p.2.2).2
    apply hf.trans
    calc
      (p.2.1.1.absNorm:ℝ)^2 ≤ (Z^B2)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) hcap2 2
      _=Z^(2*B2):=by rw [pow_two,←Real.rpow_add (zero_lt_one.trans hZ)];congr 1;ring
  have hfactor : normValue (childMultiplier left u0 units p)=normValue u0*(normValue S*normValue F*normValue G) :=by
    have hm : childMultiplier left u0 units p=u0*S*F*G*units p.1:=by
      dsimp only [childMultiplier,S,F,G]
      ring
    have hunit (x : O) : normValue (x*units p.1)=normValue x:=by
      unfold normValue
      rw [Ideal.span_singleton_mul_right_unit (hunits p.1)]
    rw [hm,hunit,normValue_mul,normValue_mul,normValue_mul]
    ring
  rw [hfactor]
  have hsF:=mul_le_mul hS hF (show 0 ≤ normValue F from Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hsFG:=mul_le_mul hsF hG (show 0 ≤ normValue G from Nat.cast_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  apply (mul_le_mul_of_nonneg_left hsFG (show 0 ≤ normValue u0 from Nat.cast_nonneg _)).trans_eq
  congr 1
  rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
  congr 1
  ring

variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- Every actual supported key, including a zero/direct source, has the
required successor cap before a child or its recursive output is selected. -/
theorem actual_inner_all_row_prefix_cap (N : ReachableNode C j)
    (left : Bool)(units : FirstSourceLabel→O)(hunits : ∀l,IsUnit (units l))
    (p : Cycle63Moment.ChildPrefix)(hC1 : Supported p.1.1.1)(hD1 : Supported p.1.1.2)
    (hC2 : Supported p.2.1.1)(hD2 : Supported p.2.1.2)
    (hCD2 : primeSupport p.2.1.1=primeSupport p.2.1.2)
    (hcap1 : (p.1.1.1.absNorm:ℝ) ≤ N.localBase^(3:ℝ))
    (hcap2 : (p.2.1.1.absNorm:ℝ) ≤ N.localBase^(130:ℝ)) :
    childMultiplier left N.presentation.mult units p≠0 ∧
      normValue (childMultiplier left N.presentation.mult units p) ≤ C.globalBase^prefixCap (j.val+1) :=by
  have hn:=actual_label_child_norm_bound N.localBase N.localBase_gt_one left N.presentation.mult units
    N.presentation.hv hunits p hC1 hD1 hC2 hD2 hCD2 3 130 hcap1 hcap2
  refine ⟨hn.1,hn.2.trans ?_⟩
  have hg0 : 0<C.globalBase:=zero_lt_one.trans C.globalBase_gt_one
  have hparent : normValue N.presentation.mult ≤ C.globalBase^prefixCap j.val:=N.presentation_global_norm
  have hlocal : N.localBase^((6:ℝ)*3+2*130) ≤ C.globalBase^(1000:ℝ) :=by
    rw [N.localBase_eq,←Real.rpow_mul hg0.le]
    apply Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le
    nlinarith only [N.unit_le_one]
  apply (mul_le_mul hparent hlocal (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le _)
    (Real.rpow_nonneg hg0.le _)).trans_eq
  rw [←Real.rpow_add hg0,prefixCap_succ]

theorem actual_root_all_row_prefix_cap (Z : ℝ)(hZ : 1<Z)
    (left : Bool)(units : FirstSourceLabel→O)(hunits : ∀l,IsUnit (units l))
    (p : Cycle63Moment.ChildPrefix)(hC1 : Supported p.1.1.1)(hD1 : Supported p.1.1.2)
    (hC2 : Supported p.2.1.1)(hD2 : Supported p.2.1.2)
    (hCD2 : primeSupport p.2.1.1=primeSupport p.2.1.2)
    (hcap1 : (p.1.1.1.absNorm:ℝ) ≤ Z^(3:ℝ))
    (hcap2 : (p.2.1.1.absNorm:ℝ) ≤ Z^(130:ℝ)) :
    childMultiplier left 1 units p≠0 ∧
      normValue (childMultiplier left 1 units p) ≤ Z^prefixCap 0 :=by
  have hn:=actual_label_child_norm_bound Z hZ left 1 units one_ne_zero hunits p hC1 hD1 hC2 hD2 hCD2 3 130 hcap1 hcap2
  refine ⟨hn.1,hn.2.trans ?_⟩
  have hone : normValue (1:O)=1:=by simp [normValue]
  rw [hone,one_mul]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  norm_num [prefixCap]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_label_child_norm_bound
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_all_row_prefix_cap
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_all_row_prefix_cap
