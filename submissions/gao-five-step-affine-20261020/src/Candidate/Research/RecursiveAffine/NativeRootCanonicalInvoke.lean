/- Actual bare ROOT source invocation, on the literal affine input and original slots.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalPaidColumns
import Candidate.Research.RecursiveAffine.NativeRootCanonicalFactory
import Candidate.Research.RecursiveAffine.NativeRootSourceGates
import Candidate.Research.RecursiveAffine.NativeFiniteDaughterSource

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
open Cycle153RootStep Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit Cycle153SourceSchedule Cycle153SourceUniform
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(C : SourceContext (α:=alpha) M H)
noncomputable local instance rootCanonicalInvokeLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- The source operator here is the genuine checked canonical producer.
Its metadata are fixed by the pre-Z finite-original-subset schedule; this
name only specializes the native numeric domain, and chooses no constants
from the moving root source. -/
def RootCanonicalNativeSpec
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ) : Prop :=by
  exact NativeCanonicalPaidColumnsAt (alpha:=alpha) (Current:=alpha) hH C.W C.W_support C.W_smooth
    C.etaSeed C.Q C.Q_le_M hQ0 hQt C.fixed_small
    1 (oldLoss epsNode) (oldLoss epsNode) (by norm_num) (oldLoss_pos hepsNode) (oldLoss_pos hepsNode)
    hbeta (0:Fin 4) (Function.Embedding.refl alpha)
    1 31 g.τ g.δ g.e g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) g.τ_pos g.δ_pos
    g.e_pos g.e_cap g.κ_pos (by norm_num) (by simpa only [mul_one] using g.budget)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol C.globalBase (Fintype.card alpha) Cs
    degreeDirect controlDirect Cdirect C0 C1 Kdirect epsNode

/-- Instantiate the real source on the literal original root input, source
character, original weights, profile controls, signed source height and
occupied canonical buffer. No row energy or detached source bound is an
input. The remaining arguments are the literal row geometry and its actual
canonical/common callback arguments. -/
def actualRootCanonicalInvocation
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : RootCanonicalNativeSpec hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (s : Input alpha)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (hm : Matches M H hH s C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 C.globalBase)
    (hwL : ∀i : alpha,C.originalWeight i≤Cycle25.Energy.commonMesh 2 28 1 (oldLoss epsNode))
    (hwr : ∀i : alpha,(C.originalWeight i)/31≤1)
    (hslots : Cycle63.AffineLedger.slotFloor ≤ ∑i,C.originalWeight i ∧
      (∑i,C.originalWeight i) ≤ Cycle63.AffineLedger.slotTop)
    (mesh : ℝ)(hmesh : 0 ≤ mesh)(hwm : ∀i,C.originalWeight i ≤ mesh)
    (height : ℝ)(hheight : 0 ≤ height)(hfreq : ∀i,|C.frequency i| ≤ height)
    (sourceHeight : ℝ)(buffer : BufferIndex g.e)(hp : 1≤buffer.1.val)
    (hSmallHeight : |sourceHeight|+height+C.globalBase^g.τ/2≤5*C.globalBase^g.τ)
    (hHigh : (3+(3*buffer.1.val+2:ℕ)*C.globalBase^g.τ)^2≤(C.globalBase^(31:ℝ))^(3:ℝ)) :=
  (show NativeCanonicalPaidColumnsAt (alpha:=alpha) (Current:=alpha) hH C.W C.W_support C.W_smooth
    C.etaSeed C.Q C.Q_le_M hQ0 hQt C.fixed_small
    1 (oldLoss epsNode) (oldLoss epsNode) (by norm_num) (oldLoss_pos hepsNode) (oldLoss_pos hepsNode)
    hbeta (0:Fin 4) (Function.Embedding.refl alpha)
    1 31 g.τ g.δ g.e g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) g.τ_pos g.δ_pos
    g.e_pos g.e_cap g.κ_pos (by norm_num) (by simpa only [mul_one] using g.budget)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol C.globalBase (Fintype.card alpha) Cs
    degreeDirect controlDirect Cdirect C0 C1 Kdirect epsNode from source)
    C rfl rfl rfl C.globalBase_gt_one 1 zero_lt_one (by rw [Real.rpow_one])
    s sourceHeight height mesh ((1+Cycle63.AffineLedger.q)/2)
    (rootDetectorDeletion C.originalWeight) buffer.1.val (by simpa only[Function.Embedding.refl_apply,div_one] using hm) (le_refl _) caps.controls caps.b₁ caps.b₂
    (by simpa only[Function.Embedding.refl_apply,div_one] using hwr) (by simpa only[Function.Embedding.refl_apply,div_one] using hwL)
    hmesh (fun i=>by simpa only[Function.Embedding.refl_apply,div_one] using hwm i) hheight hfreq
    (by linarith only [Cycle63.AffineLedger.one_fiftieth_le_q]) (le_refl _) (actual_root_canonical_scalar_gates C.originalWeight hslots).2.2.2.1
    (canonical_buffer_frequency buffer hp sourceHeight height (C.globalBase^g.τ)
      (Real.rpow_nonneg (zero_lt_one.trans C.globalBase_gt_one).le _) hSmallHeight
      (fun i : alpha=>C.frequency i) hfreq).1 hHigh

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootCanonicalInvocation
