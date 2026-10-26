/- Actual INNER source invocation, on the literal affine input and original slots.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalFactory
import Candidate.Research.RecursiveAffine.NativeFiniteDaughterSource
import Candidate.Research.RecursiveAffine.NativeNodeSourceGates
import Candidate.Research.RecursiveAffine.NativeSourceOldMesh

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open LocalMoment ConcretePrimeRowBridge CenteredMomentSecondHeightFamily Cycle153CanonicalLow
open Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit Cycle153SourceSchedule Cycle153SourceUniform
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

/-- The source operator here is the genuine checked canonical producer.
Its metadata are fixed by the pre-Z finite-original-subset schedule; this
name only specializes the native numeric domain, and chooses no constants
from the moving node. -/
def InnerCanonicalNativeSpec
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ) : Prop :=by
  letI : Cycle63.AffineLedger:=N.ledger
  exact NativeCanonicalPaidColumnsAt (alpha:=alpha) (Current:=N.slots) hH C.W C.W_support C.W_smooth
    C.etaSeed C.Q C.Q_le_M hQ0 hQt C.fixed_small
    1 (oldLoss epsNode) (oldLoss epsNode) (by norm_num) (oldLoss_pos hepsNode) (oldLoss_pos hepsNode)
    hbeta (nextInner j hj) (originalSubsetEmbedding N.slots)
    1 31 g.τ g.δ g.e g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) g.τ_pos g.δ_pos
    g.e_pos g.e_cap g.κ_pos (by norm_num) (by simpa only [mul_one] using g.budget)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol N.localBase (Fintype.card N.slots) Cs
    degreeDirect controlDirect Cdirect C0 C1 Kdirect epsNode

/-- Instantiate the real source on this node's literal `N.input`, source
character, original weights, profile controls, signed source height and
occupied canonical buffer. No row energy or detached source bound is an
input. The remaining arguments are the literal row geometry and its actual
canonical/common callback arguments. -/
def actualInnerCanonicalInvocation
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : InnerCanonicalNativeSpec hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (caps : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (hm : Matches M H hH (N.input hH) C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 N.localBase)
    (hSourceMesh : C.slotMesh≤localSlotMesh epsNode)
    (sourceHeight : ℝ)(buffer : BufferIndex g.e)(hp : 1≤buffer.1.val)
    (hSmallHeight : |sourceHeight|+N.height+N.localBase^g.τ/2≤5*N.localBase^g.τ)
    (hHigh : (3+(3*buffer.1.val+2:ℕ)*N.localBase^g.τ)^2≤(N.localBase^(31:ℝ))^(3:ℝ)) :=
  letI : Cycle63.AffineLedger:=N.ledger
  (show NativeCanonicalPaidColumnsAt (alpha:=alpha) (Current:=N.slots) hH C.W C.W_support C.W_smooth
    C.etaSeed C.Q C.Q_le_M hQ0 hQt C.fixed_small
    1 (oldLoss epsNode) (oldLoss epsNode) (by norm_num) (oldLoss_pos hepsNode) (oldLoss_pos hepsNode)
    hbeta (nextInner j hj) (originalSubsetEmbedding N.slots)
    1 31 g.τ g.δ g.e g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) g.τ_pos g.δ_pos
    g.e_pos g.e_cap g.κ_pos (by norm_num) (by simpa only [mul_one] using g.budget)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol N.localBase (Fintype.card N.slots) Cs
    degreeDirect controlDirect Cdirect C0 C1 Kdirect epsNode from source)
    C rfl rfl rfl N.localBase_gt_one N.unit N.unit_pos N.localBase_eq
    (N.input hH) sourceHeight N.height C.slotMesh ((1+Cycle63.AffineLedger.q)/2)
    (nodeDetectorDeletion N) buffer.1.val hm (le_refl _) caps.controls caps.b₁ caps.b₂
    (fun i=>by
      change C.originalWeight i/N.unit/31≤1
      have hg : (1:ℝ)≤C.gridDenominator :=by exact_mod_cast C.grid_positive
      have hm : C.slotMesh≤1 :=C.slotMesh_grid.trans ((div_le_one (by positivity)).mpr hg)
      have hw:=(N.weight_mesh i).trans hm
      linarith only [hw])
    (fun i=>(N.weight_mesh i).trans (hSourceMesh.trans (localSlotMesh_admits_old_source hepsNode)))
    C.slotMesh_pos.le N.weight_mesh N.height_nonneg N.frequency_bound
    (by linarith only [Cycle63.AffineLedger.one_fiftieth_le_q]) (le_refl _)
    (actual_node_canonical_scalar_gates N).2.2
    (canonical_buffer_frequency buffer hp sourceHeight N.height (N.localBase^g.τ)
      (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le _) hSmallHeight
      (fun i : N.slots=>C.frequency i) N.frequency_bound).1 hHigh

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerCanonicalInvocation
