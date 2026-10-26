/- Coarse bounds from the actual finite native source path. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootReturnedPayment

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount

private theorem prod_coarse_powers {Z : ℝ} (hZ : 1≤Z) (n : ℕ) (e : ℕ→ℝ)
    (he : ∀i,i<n→e i≤204) :
    (∏i∈Finset.range n,Z^e i)≤Z^(204*(n:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have h1:=ih (fun i hi=>he i (by omega))
    have h2:=Real.rpow_le_rpow_of_exponent_le hZ (he n (by omega))
    calc
      _ ≤ Z^(204*(n:ℝ))*Z^(204:ℝ) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (zero_le_one.trans hZ) _)
          (Real.rpow_nonneg (zero_le_one.trans hZ) _)
      _ = _ := by
        rw [←Real.rpow_add (zero_lt_one.trans_le hZ)]
        congr 1
        push_cast
        ring

variable {α : Type} [Fintype α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H}
  {C : SourceContext (α:=α) M H} {j : Fin 4} {N : ReachableNode C j}
  {representedBase representedUnit : ℝ}
  {F : SuffixFamily (hH:=hH) j.val (4-j.val) C.etaSeed representedBase C.Bnorm C.Tz N.presentation.mult}
  {d : SuffixDepth (4-j.val)} {p : F.Prefix d}

/-- This weight bound is derived from every actual native edge's source
gates and literal fee. It is not an additional bound on a returned family. -/
theorem ActualPathTrace.weight_coarse
    (trace : ActualPathTrace hH N representedUnit F d p) :
    F.weight d p≤C.globalBase^(204*(trace.count:ℝ)) := by
  rw [trace.weight]
  apply prod_coarse_powers C.globalBase_gt_one.le
  intro i hi
  have hc:=NativePaidPathNode.SourceGates.coarse (trace.node i) (trace.sourceGates i hi)
  have h:=NativePaidPathNode.CoarseSource.raw_edge_exponent (trace.node i) hc
    ((trace.fee i).junction*(trace.fee i).modelDeletion+(trace.fee i).amount)
    (trace.remainingFee i hi)
  rw [(trace.node_eq i hi).1]
  linarith only [h]

/-- A reachable inner source has at most three continuing LOW edges. -/
theorem ActualPathTrace.weight_coarse_global
    (trace : ActualPathTrace hH N representedUnit F d p) :
    F.weight d p≤C.globalBase^(612:ℝ) := by
  have hn : trace.count≤3 := by
    have hn:=suffixOffset_lt (4-j.val) d
    rw [←trace.count_eq] at hn
    omega
  have hnR : (trace.count:ℝ)≤3 := by exact_mod_cast hn
  exact trace.weight_coarse.trans (Real.rpow_le_rpow_of_exponent_le
    C.globalBase_gt_one.le (by linarith only [hnR]))

/-- The same bound in the actual local source base. Its unit floor is a
proved reachable-source invariant, so no configuration-specific cap is used. -/
theorem ActualPathTrace.weight_coarse_local
    {F : N.Family hH} {d : SuffixDepth (4-j.val)} {p : F.Prefix d}
    (trace : ActualPathTrace hH N N.unit F d p) :
    F.weight d p≤N.localBase^(30600:ℝ) := by
  calc
    F.weight d p≤C.globalBase^(612:ℝ) := trace.weight_coarse_global
    _ ≤C.globalBase^(N.unit*30600) := Real.rpow_le_rpow_of_exponent_le
      C.globalBase_gt_one.le (by nlinarith only [N.unit_floor])
    _ =N.localBase^(30600:ℝ) := by
      rw [N.localBase_eq,←Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]

/-- The literal root LOW edge followed by the actual inner path has at
most four continuing edges. Every raw normalizer is retained in the weight. -/
theorem root_trace_weight_coarse
    (N : ReachableNode C (0:Fin 4))
    (F : SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz N.presentation.mult)
    (d : SuffixDepth 4) (p : F.Prefix d)
    (trace : ActualPathTrace hH N 1 F d p)
    (edge : RootTraceEdge (C:=C) trace.coordinates
      (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0)) :
    C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
      edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)*F.weight d p≤
      C.globalBase^(816:ℝ) := by
  have hc:=NativePaidPathNode.SourceGates.coarse edge.node edge.sourceGates
  have h:=NativePaidPathNode.CoarseSource.raw_edge_exponent edge.node hc
    (edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount) edge.remainingFee
  have he : C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
      edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)≤C.globalBase^(204:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le
    linarith only [h]
  calc
    _ ≤C.globalBase^(204:ℝ)*C.globalBase^(612:ℝ) :=
      mul_le_mul he trace.weight_coarse_global (F.weight_nonneg d p)
        (Real.rpow_nonneg (zero_lt_one.trans C.globalBase_gt_one).le _)
    _ =_ := by rw [←Real.rpow_add (zero_lt_one.trans C.globalBase_gt_one)];norm_num

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.ActualPathTrace.weight_coarse
#print axioms OAI.SevenEighths.Cycle153Reachable.root_trace_weight_coarse
