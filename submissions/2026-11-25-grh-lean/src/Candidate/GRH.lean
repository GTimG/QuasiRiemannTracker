import Candidate.New.Main

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000
-- The proof is Levent Alpöge's, with Claude.

theorem riemannHypothesis : RiemannHypothesis := New.zeta_zeros_on_line New.grh

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := New.grh

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := New.zeros_on_line New.grh

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ ↦ LFunction_eq_zero_re N χ
