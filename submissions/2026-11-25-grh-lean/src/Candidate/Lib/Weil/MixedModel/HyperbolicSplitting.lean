import Candidate.Lib.Weil.MixedModel.ZeroTermLaw

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Standard polarisation of the hyperbolic space as a splitting. -/

/-- The splitting of hyperbolic space of rank 2p over the zero space, with l the first p and k
the last p basis vectors. -/
noncomputable def hyperbolicSplitting E p [Field E] [CMType E] [WeilData E] [Fintype p] :
  (hypSpace E p).Splitting (stdSpace E Empty)
  p := by use .fromRows 0 1, .fromRows 1 0, 0 <;> first | (ext ⟨⟩; done) | simp +arith
