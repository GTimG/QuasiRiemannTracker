/- Terminal caps from the actual own-HIGH source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceTerminal
import Candidate.Research.RecursiveAffine.ActualReachableHigh

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle153SourceReturn
open CenteredMomentAmplificationChildInput Cycle63InitialSource Cycle63Moment QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentFirstSourceReduction
open CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentInductionEnergy

theorem TerminalSourceCaps.scale {scale length amp normLog u : ℝ}
    (caps : TerminalSourceCaps scale length amp normLog) (hu : 0≤u) (hu1 : u≤1) :
    TerminalSourceCaps (u*scale) (u*length) (u*amp) (u*normLog) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left caps.scale_le hu).trans (by simpa using hu1)
  · exact (mul_le_mul_of_nonneg_left caps.length_le hu).trans (by linarith only [hu1])
  · exact (mul_le_mul_of_nonneg_left caps.amp_le hu).trans (by simpa using hu1)
  · exact (mul_le_mul_of_nonneg_left caps.normLog_le hu).trans (by linarith only [hu1])

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H}
  {C : SourceContext (α:=α) M H} {j : Fin 4}

theorem ReachableNode.actual_volume_le_one (N : ReachableNode C j) :
    Real.logb N.localBase (volume (N.input hH))≤1 := by
  letI : Cycle63.AffineLedger:=N.ledger
  have hz : 0≤∑i : N.slots,C.originalWeight i/N.unit :=
    Finset.sum_nonneg (fun i _=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
  have hv:=N.window.volume_le hz
  have hlog : Real.logb N.localBase (volume (N.input hH))=
      length N.localBase N.X1+length N.localBase N.X2+∑i : N.slots,C.originalWeight i/N.unit := by
    apply mul_left_cancel₀ N.unit_pos.ne'
    exact (N.volume_model (hH:=hH)).trans N.length_eq.symm
  rw [hlog]
  exact hv

theorem ReachableNode.actual_amp_le_one (N : ReachableNode C j) :
    letI : Cycle63.AffineLedger:=N.ledger
    Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))≤1 := by
  letI : Cycle63.AffineLedger:=N.ledger
  have hc:=Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩
  exact (Cycle63.AffineLedger.amp_bounds
    (Cycle63.AffineLedger.cellUpper_bounds hc.1 hc.2.1)).2.trans
      Cycle63.AffineLedger.amplifierCap_le_one

theorem ReachableNode.actual_prefix_log_coarse (N : ReachableNode C j) :
    Real.logb N.localBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ)≤250000 := by
  have hp : (0:ℝ)<((Ideal.span {N.presentation.mult}).absNorm:ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr N.presentation.hv)))
  apply (Real.logb_le_iff_le_rpow N.localBase_gt_one hp).mpr
  calc
    ((Ideal.span {N.presentation.mult}).absNorm:ℝ)≤C.globalBase^prefixCap j.val :=
      N.presentation_global_norm
    _ ≤C.globalBase^(N.unit*250000) := Real.rpow_le_rpow_of_exponent_le
      C.globalBase_gt_one.le (by
        have hcap:=prefixCap_le_four j
        nlinarith only [hcap,N.unit_floor])
    _ =N.localBase^(250000:ℝ) := by
      rw [N.localBase_eq,←Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]

/-- The terminal receipt follows from the SAME native own-HIGH part's
physical equalities. Its four caps are source facts and survive later
record shifts or exact base transport. -/
theorem actual_own_terminal_source_caps (N : ReachableNode C j)
    (part : ReturnedPartAt M H hH (innerStage j.val).q
      (prefixDictionary (j.val+1)) C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (hm : part.scale=N.state.rowWidth)
    (hA : part.length=Real.logb N.localBase (volume (N.input hH)))
    (ha : letI : Cycle63.AffineLedger:=N.ledger
      part.amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))) :
    TerminalSourceCaps part.scale part.length part.amp
      (Real.logb N.localBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ)) := by
  refine ⟨?_,?_,?_,N.actual_prefix_log_coarse⟩
  · rw [hm]
    have hc:=N.state.character_nonneg
    have hw:=N.width_le_one
    unfold NaturalState.width at hw
    linarith only [hc,hw]
  · rw [hA]
    exact (N.actual_volume_le_one).trans (by norm_num)
  · rw [ha]
    exact N.actual_amp_le_one

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_own_terminal_source_caps
