/- Genuine pre-Z terminal HIGH, LOW and AtState source schedules.
Copyright (c) 2026 Zhongpai Gao. Native analytic estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeTerminalUniform
import Candidate.Research.RecursiveAffine.SourceContextHighPrimitive

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open CenteredMomentNaturalFixedRaySource
open Filter HeckeFamily Cycle63InitialMass Cycle153Reachable Cycle153RegionalLow
open Cycle153RegionalState Cycle153RecursiveHighProvider Cycle153SourceSchedule
open Cycle153.RegionalSchedule
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

abbrev terminalLedger (i : TerminalGridIndex) :=
  Cycle153.regionalFamily Cycle153.FixedStages.stage4 gridSize i

/-- All native source metadata are chosen at a fixed grid ledger before
Z, the surviving slots, and the moving physical source. The stored source
statements are actual producer conclusions, rather than energy hypotheses. -/
structure TerminalNativeSchedule
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (eps tau B : ℝ)(heps : 0<eps)(eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(i : TerminalGridIndex) where
  g : GeometryAffineLowSchedule
  mu : g.μ=nativeMu
  delta : g.δ=nativeDriverRate (Fintype.card alpha)
  cutoff : 2*g.τ<tau
  Psi : 𝓢(ℝ,ℂ)
  Psi_support : Function.support (Psi:ℝ→ℂ)⊆Set.Icc (-1) (2+1)
  Psi_nonnegative : ∀x,0≤(Psi x).re
  SH : Finset (ℕ×ℕ)
  dh : ℕ
  Kclass : ℝ
  Kh : ℝ
  Kh_nonnegative : 0≤Kh
  Cs : ℝ
  Cs_one : 1≤Cs
  Sp : Finset alpha→Finset (ℕ×ℕ)
  degreeLow : Finset alpha→ℕ
  Klow : Finset alpha→ℝ
  Klow_nonnegative : ∀J,0≤Klow J
  degree : ℕ
  control : Finset (ℕ×ℕ)
  Cenergy : ℝ
  Cenergy_positive : 0<Cenergy
  Chigh : ℝ
  Chigh_nonnegative : 0≤Chigh
  actualAtState : ∀ᶠZ : ℝ in atTop,
    letI : Cycle63.AffineLedger:=terminalLedger i
    RegionalAtState (α:=alpha) M H hH W hW hWs hbeta hbetaHi g 2 20
      (localSlotMesh eps) (oldLoss eps) (by norm_num) Psi SH dh degree control Cenergy Chigh Cs
      Sp degreeLow Klow (by norm_num) (localSlotMesh_pos heps).le
      eta Q hQM hQ72 Z
  actualLow : ∀ᶠZ : ℝ in atTop,∀J,
    TerminalLowSourceAt hH W hbeta g Cs eta Q hQM hQ72 i J (Sp J) (degreeLow J) (Klow J) Z
  actualHigh : ∀ᶠZ : ℝ in atTop,
    letI : Cycle63.AffineLedger:=terminalLedger i
    ActualHighNodeAt (base:=prefixDictionary 3) (α:=alpha) M H hH W hW hWs hbeta hbetaHi
      g (1/4) (9/4) 2 20 (localSlotMesh eps) (oldLoss eps) tau B
      (highSourceLossNeeded primitiveError (Fintype.card alpha)) (by norm_num)
      Psi SH dh Kclass Kh eta Q hQM hQ72 Z

/-- The genuine HIGH producer, native OLD terminal theorem, and native
AtState theorem are composed in their required quantifier order. In
particular the radial majorant is chosen before the HIGH constants, and
all constants precede the moving base. -/
theorem terminal_native_schedule_exists
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (eps tau B : ℝ)(heps : 0<eps)(htau : 0<tau)
    (eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(i : TerminalGridIndex) :
    Nonempty (TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 i) := by
  letI : Cycle63.AffineLedger:=terminalLedger i
  have hreserve : 128*nativeMu≤Cycle63.AffineLedger.lowReserve := regional_native_reserve (4:Fin 5) i
  have hmesh:=regional_source_mesh_gates heps (4:Fin 5) i
  have hq0 : Cycle63.Arithmetic.q0≤(7/10:ℝ) := by
    linarith only [Cycle63.Arithmetic.q0_bounds.2]
  have hq : Cycle63.Arithmetic.q0≤Cycle63.AffineLedger.q := by
    change Cycle63.Arithmetic.q0≤Cycle153.FixedStages.stage4.q
    norm_num only [Cycle153.FixedStages.stage4]
    linarith only [hq0]
  obtain ⟨g,hmu,hdelta,hcut,hHigh⟩:=actual_high_node_producer (base:=prefixDictionary 3) (α:=alpha)
    M H hH primitiveError actual_high_primitive_upper W hW hWs hbeta hbetaHi
    (localSlotMesh eps) tau B primitiveError_pos (localSlotMesh_pos heps).le
    (by simpa only [actual_high_primitive_mu] using hmesh.2.2.1) htau
    eta Q hQM hQ0 hQt hQ72 hq
  have hmu' : g.μ=nativeMu := hmu.trans actual_high_primitive_mu
  have hdelta' : g.δ=nativeDriverRate (Fintype.card alpha) := by
    simpa only [actual_high_primitive_mu,nativeDriverRate] using hdelta
  have hAtdelta : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card alpha:ℝ)+2)) (Fintype.card alpha) := by
    rw [hmu'];exact hdelta'
  obtain ⟨Psi,hPsi,hPsipos,hAt⟩:=chosen_small_error_at_state (alpha:=alpha) M H hH W hW hWs
    hbeta hbetaHi g 2 20 (localSlotMesh eps) eps primitiveError_pos hmu hAtdelta
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (localSlotMesh_pos heps).le (oldLoss_pos heps)
  obtain ⟨Cs,hCs,hAt⟩:=@hAt (terminalLedger i) hmesh.1 (by simpa only [hmu'] using hreserve)
    (by simpa only [hmu',show (28:ℝ)+20=48 by norm_num] using hmesh.2.1)
    hmesh.2.2.2 eta Q hQM hQ0 hQt hQ72
  obtain ⟨Spall,degreeLowAll,KlowAll,hKlowAll,hLowAll⟩:=eventual_terminal_low_finite (alpha:=alpha)
    hH W hW hWs hbeta g Cs hCs eta Q hQM hQ0 hQt hQ72
  obtain ⟨SH,dh,Kclass,hHigh⟩:=hHigh Psi hPsi hPsipos
  obtain ⟨Kh,hKh,hHigh⟩:=hHigh (oldLoss eps) (oldLoss_pos heps)
  obtain ⟨degree,S,hSH,hdh,Cenergy,Chigh,hCenergy,hChigh,hAt⟩:=
    hAt (Spall i) (degreeLowAll i) (KlowAll i) (hKlowAll i) SH dh
  refine ⟨{
    g:=g,mu:=hmu',delta:=hdelta',cutoff:=hcut,Psi:=Psi,Psi_support:=hPsi,Psi_nonnegative:=hPsipos,
    SH:=SH,dh:=dh,Kclass:=Kclass,Kh:=Kh,Kh_nonnegative:=hKh,Cs:=Cs,Cs_one:=hCs,
    Sp:=Spall i,degreeLow:=degreeLowAll i,Klow:=KlowAll i,Klow_nonnegative:=hKlowAll i,
    degree:=degree,control:=S,Cenergy:=Cenergy,Cenergy_positive:=hCenergy,
    Chigh:=Chigh,Chigh_nonnegative:=hChigh,actualAtState:=hAt,
    actualLow:=?_,actualHigh:=hHigh}⟩
  filter_upwards [hLowAll] with Z hZ
  exact hZ i

/-- The literal returned loss, including the independent OLD epsilon,
is inside the terminal allowance. No arbitrary loss cap is assumed. -/
theorem terminal_native_loss_bound {eps : ℝ} (heps : 0<eps) :
    highSourceLossNeeded primitiveError (Fintype.card alpha)+oldLoss eps≤
      terminalLossCap (3:Fin 4) := by
  have hl:=actual_high_primitive_loss (Fintype.card alpha)
  have he:=(oldLoss_bounds eps).2
  apply le_trans (add_le_add hl he)
  norm_num [terminalLossCap,nativeMu,primitiveError]

end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.terminal_native_schedule_exists
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.terminal_native_loss_bound
