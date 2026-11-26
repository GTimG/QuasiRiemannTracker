import Candidate.Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
import Candidate.Lib.DiscreteSeries.Haar.SphereFibreIntegral
import Candidate.Lib.Adelic.QuotientMeasure.CocompactIntegrable

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: U(n) has total mass one; the measure on U(J) is right invariant. -/


open MeasureTheory Measure Fintype
variable {n} [Fintype.{0} n]

/-- U(n) has mass 1 (the Cayley density has integral `volU n`): one column at a time.

Known result: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume
growth. -/
instance isProbabilityMeasure_haarU : @IsProbabilityMeasure (U (1 : Matrix n n ℂ)) _ volume := ⟨by
  simp [← lintegral_one, ↓lintegral_eq_cayleyChart]
  induction' hk : card n with k ih generalizing n
  rw [card_eq_zero_iff] at hk; simpa [volU] using! pi_empty_univ _
  erw [volU, Finset.prod_range_succ_comm,
    ← (skewColumnEquiv_spec ((equivFinOfCardEq hk).2 0)).1.lintegral_comp, lintegral_prod_symm,
    funext (hk ▸ lintegral_cayleyDensity_skewColumnEquiv _ · (volU_pos k) :), ih] <;> measurability⟩

instance :
  @IsProbabilityMeasure (U (@signMatrix n 1)) _ volume := by rw! [signMatrix_one]; infer_instance

instance {J} [@IsHermInvolution n _ J] : (@volume (U J) _).IsMulRightInvariant :=
  ⟨(measurePreserving_haarU 1 · 1 (.mulRight _) |>.2)⟩
