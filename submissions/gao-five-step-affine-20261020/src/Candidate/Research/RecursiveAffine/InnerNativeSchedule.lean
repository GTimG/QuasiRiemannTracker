/- Actual inner HIGH and AtState schedules precede the recursive LOW source.
Copyright (c) 2026 Zhongpai Gao. Native estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.TerminalNativeApply

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalFixedRaySource Cycle63InitialMass
open Cycle153Reachable Cycle153RegionalLow Cycle153RegionalState
open Cycle153RecursiveHighProvider Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153.RegionalSchedule
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

abbrev InnerGridIndex (j : Fin 4) :=Cycle153.RegionalIndex (innerStage j.val) gridSize
abbrev innerLedger (j : Fin 4)(i : InnerGridIndex j) :=Cycle153.regionalFamily (innerStage j.val) gridSize i

private theorem inner_reserve (j : Fin 4)(i : InnerGridIndex j) :
    128*nativeMu ≤ @Cycle63.AffineLedger.lowReserve (innerLedger j i) := by
  fin_cases j
  · exact regional_native_reserve (1:Fin 5) i
  · exact regional_native_reserve (2:Fin 5) i
  · exact regional_native_reserve (3:Fin 5) i
  · exact regional_native_reserve (4:Fin 5) i

private theorem inner_native_junction (j : Fin 4)(i : InnerGridIndex j) :
    Cycle63.Arithmetic.q0 ≤ @Cycle63.AffineLedger.q (innerLedger j i) := by
  have hq0 : Cycle63.Arithmetic.q0 ≤ (2/3:ℝ) := by linarith only [Cycle63.Arithmetic.q0_bounds.2]
  apply hq0.trans
  change (2/3:ℝ) ≤ (innerStage j.val).q
  fin_cases j <;> norm_num [innerStage,Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
    Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4]

/-- HIGH production and the native AtState upper operator are genuinely
chosen before a recursive LOW source is supplied. The latter will provide
only its profile metadata and literal LOW receipt; no future energy bound
is installed as a field of this native schedule. -/
structure InnerNativeSchedule
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)
    (eps tau B : ℝ)(heps : 0<eps)(eta : Character)(Q : Ideal O)(hQM : Q ≤ M)
    (hQ72 : internalQ Q eta ≤ Ideal.span {(72:O)})(j : Fin 4)(i : InnerGridIndex j) where
  g : GeometryAffineLowSchedule
  mu : g.μ=nativeMu
  delta : g.δ=nativeDriverRate (Fintype.card alpha)
  cutoff : 2*g.τ<tau
  Psi : 𝓢(ℝ,ℂ)
  Psi_support : Function.support (Psi:ℝ→ℂ)⊆Set.Icc (-1) (2+1)
  Psi_nonnegative : ∀x,0 ≤ (Psi x).re
  SH : Finset (ℕ×ℕ)
  dh : ℕ
  Kclass : ℝ
  Kh : ℝ
  Kh_nonnegative : 0 ≤ Kh
  Cs : ℝ
  Cs_one : 1 ≤ Cs
  actualHigh : ∀ᶠZ : ℝ in atTop,
    letI : Cycle63.AffineLedger:=innerLedger j i
    ActualHighNodeAt (base:=prefixDictionary j.val) (α:=alpha) M H hH W hW hWs hbeta hbetaHi
      g (1/4) (9/4) 2 20 (localSlotMesh eps) (oldLoss eps) tau B
      (highSourceLossNeeded primitiveError (Fintype.card alpha)) (by norm_num)
      Psi SH dh Kclass Kh eta Q hQM hQ72 Z
  actualAtState :
    ∀(Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)(Klow : Finset alpha→ℝ),
      (∀J,0 ≤ Klow J)→
    ∃(degree : ℕ)(control : Finset (ℕ×ℕ)),SH⊆control ∧ dh ≤ degree ∧
    ∃Cenergy Chigh : ℝ,0<Cenergy ∧ 0 ≤ Chigh ∧ ∀ᶠZ : ℝ in atTop,
      letI : Cycle63.AffineLedger:=innerLedger j i
      RegionalAtState (α:=alpha) M H hH W hW hWs hbeta hbetaHi g 2 20
        (localSlotMesh eps) (oldLoss eps) (by norm_num) Psi SH dh degree control Cenergy Chigh Cs
        Sp degreeLow Klow (by norm_num) (localSlotMesh_pos heps).le eta Q hQM hQ72 Z

/-- A direct native producer for every fixed inner grid ledger. All
source constants precede the moving base, and the same literal masked
prefix will later be supplied by the actual reachable node. -/
theorem inner_native_schedule_exists
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)
    (eps tau B : ℝ)(heps : 0<eps)(htau : 0<tau)
    (eta : Character)(Q : Ideal O)(hQM : Q ≤ M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta ≤ Ideal.span {(72:O)})(j : Fin 4)(i : InnerGridIndex j) :
    Nonempty (InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 j i) := by
  letI : Cycle63.AffineLedger:=innerLedger j i
  have hreserve : 128*nativeMu ≤ Cycle63.AffineLedger.lowReserve :=inner_reserve j i
  have hmesh:=@local_native_mesh_gates (innerLedger j i) eps 20 heps (by norm_num) le_rfl hreserve
  obtain ⟨g,hmu,hdelta,hcut,hHigh⟩:=actual_high_node_producer (base:=prefixDictionary j.val) (α:=alpha)
    M H hH primitiveError actual_high_primitive_upper W hW hWs hbeta hbetaHi
    (localSlotMesh eps) tau B primitiveError_pos (localSlotMesh_pos heps).le
    (by simpa only [actual_high_primitive_mu] using hmesh.2.2.1) htau
    eta Q hQM hQ0 hQt hQ72 (inner_native_junction j i)
  have hmu' : g.μ=nativeMu :=hmu.trans actual_high_primitive_mu
  have hdelta' : g.δ=nativeDriverRate (Fintype.card alpha) := by
    simpa only [actual_high_primitive_mu,nativeDriverRate] using hdelta
  have hAtdelta : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card alpha:ℝ)+2)) (Fintype.card alpha) := by rw [hmu'];exact hdelta'
  obtain ⟨Psi,hPsi,hPsipos,hAt⟩:=chosen_small_error_at_state (alpha:=alpha) M H hH W hW hWs
    hbeta hbetaHi g 2 20 (localSlotMesh eps) eps primitiveError_pos hmu hAtdelta
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (localSlotMesh_pos heps).le (oldLoss_pos heps)
  obtain ⟨Cs,hCs,hAt⟩:=@hAt (innerLedger j i) hmesh.1 (by simpa only [hmu'] using hreserve)
    (by simpa only [hmu'] using hmesh.2.1) hmesh.2.2.2 eta Q hQM hQ0 hQt hQ72
  obtain ⟨SH,dh,Kclass,hHigh⟩:=hHigh Psi hPsi hPsipos
  obtain ⟨Kh,hKh,hHigh⟩:=hHigh (oldLoss eps) (oldLoss_pos heps)
  refine ⟨{
    g:=g,mu:=hmu',delta:=hdelta',cutoff:=hcut,Psi:=Psi,Psi_support:=hPsi,
    Psi_nonnegative:=hPsipos,SH:=SH,dh:=dh,Kclass:=Kclass,Kh:=Kh,Kh_nonnegative:=hKh,
    Cs:=Cs,Cs_one:=hCs,actualHigh:=hHigh,actualAtState:=?_}⟩
  intro Sp degreeLow Klow hKlow
  exact hAt Sp degreeLow Klow hKlow SH dh

end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.inner_native_schedule_exists
