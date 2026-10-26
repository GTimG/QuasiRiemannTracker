/- Genuine ROOT canonical metadata before the original subset, source context and base.
Copyright (c)2026 Zhongpai Gao. Native source operators by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootCanonicalInvoke
import Candidate.Research.RecursiveAffine.NativeCanonicalPaidColumns
import Candidate.Research.RecursiveAffine.FiniteSourceUniformization
import Candidate.Research.RecursiveAffine.SourceContextFee

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RootLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle63InitialMass Cycle153Reachable Cycle153ActualColumn Cycle153RegionalLow
open Cycle153SourceSchedule Cycle153SourceUniform
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)
variable (eta : Character)(Q : Ideal O)(hQM : Q≤M)
variable (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})
variable (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)
variable (hCs : 1≤Cs)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
noncomputable local instance rootCanonicalMetadataLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
attribute [local irreducible] NativeCanonicalPaidColumnsAt

/-- The real ROOT source on the original subset as its OWN ambient type.
Its child embedding is literally reflexive and its column budget is the
literal subset cardinal. The positive driver and post rate remain the
fixed ambient schedule supplied before any moving context. -/
def RootCanonicalSubsetAt (T : Finset alpha)
    (dt dd : ℕ)(ct cd : Finset (ℕ×ℕ))(Kt Cp Kc Cd C0 C1 Kd Z : ℝ) : Prop :=
  ∀C : SourceContext (α:=T) M H,C.W=W→C.etaSeed=eta→C.Q=Q→C.globalBase=Z→
    ∀(hQ0C : internalQ C.Q C.etaSeed≠0)(hQtC : internalQ C.Q C.etaSeed≠⊤),
      RootCanonicalNativeSpec hH C hQ0C hQtC hbeta g Cs epsNode epsShell hepsNode hShell
        dt ct Kt Cp Kc dd cd Cd C0 C1 Kd

/- Invoke the genuine canonical producer separately on each original
subset with alpha=Current=T. Every degree, control set and positive
constant is selected before Z or C; no energy or RAW premise is used. -/
include hW hWs hQM hQ0 hQt hQ72 hCs in
theorem actual_root_canonical_metadata :
    ∃(dt dd : Finset alpha→ℕ)(ct cd : Finset alpha→Finset (ℕ×ℕ))
      (Kt Cp Kc Cd C0 C1 Kd : Finset alpha→ℝ),
      (∀T,0<Kt T ∧1≤Cp T ∧0<Kc T ∧1≤Cd T ∧0<C0 T ∧0<C1 T ∧0<Kd T) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧∀T : Finset alpha,
        RootCanonicalSubsetAt hH W hbeta eta Q g Cs epsNode epsShell hepsNode hShell T
          (dt T) (dd T) (ct T) (cd T) (Kt T) (Cp T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T) Z :=by
  have produce : ∀T : Finset alpha,
      ∃(dt dd : ℕ)(ct cd : Finset (ℕ×ℕ))(Kt Cp Kc Cd C0 C1 Kd : ℝ),
      (0<Kt ∧1≤Cp ∧0<Kc ∧1≤Cd ∧0<C0 ∧0<C1 ∧0<Kd) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        RootCanonicalSubsetAt hH W hbeta eta Q g Cs epsNode epsShell hepsNode hShell T
          dt dd ct cd Kt Cp Kc Cd C0 C1 Kd Z :=by
    intro T
    obtain ⟨dt,ct,Kt,Cp,Kc,dd,cd,Cd,C0,C1,Kd,hKt,hCp,hKc,hCd,hC0,hC1,hKd,hs⟩:=
      eventual_actual_canonical_paid_columns (alpha:=T) (Current:=T)
        hH W hWs hW eta Q hQM hQ0 hQt hQ72
        1 (oldLoss epsNode) (oldLoss epsNode) (by norm_num)
        (oldLoss_pos hepsNode) (oldLoss_pos hepsNode)
        hbeta (0:Fin 4) (Function.Embedding.refl T)
        1 31 g.τ g.δ g.e g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) g.τ_pos g.δ_pos
        g.e_pos g.e_cap g.κ_pos (by norm_num) (by simpa only [mul_one] using g.budget)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
        (Fintype.card T) Cs hCs epsNode hepsNode rfl le_rfl le_rfl
    refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd⟩,?_⟩
    filter_upwards [hs] with Z hz
    refine ⟨hz.1,?_⟩
    intro C hCW hCeta hCQ hbase hQ0C hQtC
    simpa only [RootCanonicalNativeSpec,←hCW,←hCeta,←hCQ,←hbase] using hz.2
  choose dt dd ct cd Kt Cp Kc Cd C0 C1 Kd hpositive hsource using produce
  refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,hpositive,?_⟩
  filter_upwards [Filter.eventually_all.mpr hsource] with Z hz
  exact ⟨(hz ∅).1,fun T=>(hz T).2⟩

end
end OAI.SevenEighths.Cycle153RootLowSchedule
#print axioms OAI.SevenEighths.Cycle153RootLowSchedule.actual_root_canonical_metadata
