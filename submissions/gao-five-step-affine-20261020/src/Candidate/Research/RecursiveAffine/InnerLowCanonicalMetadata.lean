/- Genuine INNER LOW canonical metadata, before moving nodes and bases. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeFiniteCanonical
import Candidate.Research.RecursiveAffine.InnerNativeSchedule
import Candidate.Research.RecursiveAffine.PhysicalStepCoordinates

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153InnerLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle153RegionalLow Cycle153SourceUniform Cycle153SourceSchedule
open Cycle153TerminalSchedule Cycle153Reachable Cycle153ActualColumn
attribute [local irreducible] NativeCanonicalPaidColumnsAt
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
variable (eps tau Bnorm : ℝ)(heps : 0<eps)(eta : Character)(Q : Ideal O)
variable (hQM : Q≤M)(hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(j : Fin 4)(hj : j.val<3)
variable (i : InnerGridIndex j)
variable (S : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
  eps tau Bnorm heps eta Q hQM hQ72 j i)

/-- The literal source uses the actual subset cardinal in its physical
column coefficient, while the native driver remains the ambient schedule. -/
def InnerCanonicalSubsetAt (epsShell : ℝ)(hShell : 0<epsShell)(T : Finset alpha)
    (dt dd : ℕ)(ct cd : Finset (ℕ×ℕ))(Kt Cp Kc Cd C0 C1 Kd Z : ℝ) : Prop :=by
  letI : Cycle63.AffineLedger:=innerLedger j i
  exact NativeCanonicalPaidColumnsAt (Current:=T) hH W hWs hW eta Q hQM hQ0 hQt hQ72
    1 (oldLoss eps) (oldLoss eps) (by norm_num) (oldLoss_pos heps) (oldLoss_pos heps)
    hbeta (nextInner j hj) (originalSubsetEmbedding T)
    1 31 S.g.τ S.g.δ S.g.e S.g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) S.g.τ_pos S.g.δ_pos
    S.g.e_pos S.g.e_cap S.g.κ_pos (by norm_num) (by simpa only [mul_one] using S.g.budget)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
    dt ct Kt Cp Kc Z T.card S.Cs dd cd Cd C0 C1 Kd eps

/-- Choose the actual terminal/direct source metadata on every ORIGINAL
subset before Z and every moving SourceContext. All real rebase units are
covered by one cutoff. No future source energy or LOW receipt is a field. -/
theorem actual_inner_canonical_metadata
    (epsShell : ℝ)(hShell : 0<epsShell) :
    ∃(dt dd : Finset alpha→ℕ)(ct cd : Finset alpha→Finset (ℕ×ℕ))
      (Kt Cp Kc Cd C0 C1 Kd : Finset alpha→ℝ),
      (∀T,0<Kt T ∧ 1≤Cp T ∧ 0<Kc T ∧ 1≤Cd T ∧0<C0 T ∧0<C1 T ∧0<Kd T) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧∀U : ℝ,(1/50:ℝ)≤U→∀T : Finset alpha,
        InnerCanonicalSubsetAt hH W hW hWs hbeta hbetaHi eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72
          j hj i S epsShell hShell T (dt T) (dd T) (ct T) (cd T)
          (Kt T) (Cp T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T) (Z^U) :=by
  letI : Cycle63.AffineLedger:=innerLedger j i
  have produce : ∀T : Finset alpha,
      ∃(dt dd : ℕ)(ct cd : Finset (ℕ×ℕ))(Kt Cp Kc Cd C0 C1 Kd : ℝ),
      (0<Kt ∧1≤Cp ∧0<Kc ∧1≤Cd ∧0<C0 ∧0<C1 ∧0<Kd) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧ InnerCanonicalSubsetAt hH W hW hWs hbeta hbetaHi
        eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72 j hj i S epsShell hShell T
        dt dd ct cd Kt Cp Kc Cd C0 C1 Kd Z :=by
    intro T
    obtain ⟨dt,ct,Kt,Cp,Kc,dd,cd,Cd,C0,C1,Kd,hKt,hCp,hKc,hCd,hC0,hC1,hKd,hs⟩:=
      eventual_actual_canonical_paid_columns (Current:=T) hH W hWs hW eta Q hQM hQ0 hQt hQ72
        1 (oldLoss eps) (oldLoss eps) (by norm_num) (oldLoss_pos heps) (oldLoss_pos heps)
        hbeta (nextInner j hj) (originalSubsetEmbedding T)
        1 31 S.g.τ S.g.δ S.g.e S.g.κ 3 2 28 1 31 Cycle63.AffineLedger.q
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) S.g.τ_pos S.g.δ_pos
        S.g.e_pos S.g.e_cap S.g.κ_pos (by norm_num) (by simpa only [mul_one] using S.g.budget)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        Cycle63.AffineLedger.q_pos.le Cycle63.AffineLedger.q_le_one (9/4) epsShell hShell
        T.card S.Cs S.Cs_one eps heps rfl le_rfl le_rfl
    exact ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd⟩,hs⟩
  choose dt dd ct cd Kt Cp Kc Cd C0 C1 Kd hpositive hs using produce
  refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,hpositive,?_⟩
  have huniform:=eventually_all_rebased_sources _ (Filter.eventually_all.mpr hs)
  filter_upwards [huniform] with Z hz
  exact ⟨hz.1,fun U hU T=>(hz.2 U hU T).2⟩

end
end OAI.SevenEighths.Cycle153InnerLowSchedule
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.actual_inner_canonical_metadata
