/- The actual initial seed supplies the marked root HIGH schedule.
Native analytic source theory (c) 2026 Hailey Collet; binding (c) 2026 Zhongpai Gao.
Released under Apache-2.0, retaining all inherited notices. -/
import Candidate.Research.RecursiveAffine.RootHighCappedSchedule
import Candidate.Research.RecursiveAffine.NativeRootParentPresentation
import Candidate.Research.RecursiveAffine.RootLedgerBinding
import Candidate.Research.RecursiveAffine.SourceContextFee

noncomputable local instance rootInitialHighLedger : Cycle63.AffineLedger := Cycle153.Root.rootLedger
local instance rootInitialHighBinding : Cycle153.MarkedRootPrice.RootLedgerBinding rootInitialHighLedger :=
  Cycle153.MarkedRootPrice.fixedRootLedgerBinding

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153RootInitialHigh
noncomputable section
open scoped Classical ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve HeckeRowClosure CanonicalRowCompletion ActualEisensteinCubic
open ConcretePrimeRowBridge Cycle63Moment CenteredMomentSecondHeightFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open Cycle63InitialMass Cycle153SourceSchedule Cycle153Reachable

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The root marked HIGH source is built from the genuine fixed seed row.
The height cap precedes all subset dictionaries, constants, Q and moving Z.
The conclusion is the literal HIGH spec needed by the root live budget;
there is no assumed source-energy or cardinality bound. -/
theorem actual_initial_root_high_schedule
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (hbetaLo : 51/100 ≤ HeckeZeroSupremum.beta)
    (hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)
    (eta : Character) (heta : eta.modulus ≤ Ideal.span {fixedBadMask})
    (hEta : excluded eta 1 = eta)
    (bPhi globalTau : ℝ) (hbPhi : 2 ≤ bPhi) (hTau : 0 < globalTau) :
    ∃g : GeometryAffineLowSchedule,
      g.μ = nativeMu ∧ g.δ = nativeDriverRate (Fintype.card alpha) ∧
      2*g.τ < globalTau ∧
      ∀T : Finset alpha, ∃P : HighSourceParameters,
        P.e = g.e ∧ P.τ = g.τ ∧
        ∃SH : Finset (ℕ × ℕ), ∃dh : ℕ, ∃KH : ℝ, 0 ≤ KH ∧
        ∀(Q : Ideal O) (hQM : Q ≤ M)
          (hQ72 : internalQ Q eta ≤ Ideal.span {(72 : O)}),
          ∀ᶠZ : ℝ in atTop,
            Cycle153RootHigh.GeometryAffineMainHighSpec (α := T) M H hH W hW.continuous hWs
              hbetaLo P g.μ g.δ (Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ)
              eta SH dh KH eta Q hQM hQ72 Z := by
  have hMarked : 2*HeckeZeroSupremum.beta-1 ≤ Cycle63.Optimization.plainCapacityCost := by
    unfold Cycle63.Optimization.plainCapacityCost
    linarith only [hbetaHi]
  have hMuCap : nativeMu ≤ Cycle63.Optimization.geometryLossCap := by
    have h := Cycle153.RegionalSchedule.primitive_marked_cap (0 : Fin 5)
    rw [Cycle153.RegionalSchedule.primitive_stageMu] at h
    exact h
  obtain ⟨tau,htau,htauMu,htauCap,g,hmu,hdelta,hgtau,hsubsets⟩ :=
    Cycle153RootHigh.actual_root_high_uniform_literal_schedule_capped (α := alpha) M H hH
      eta 1 (actualRootParentRow eta heta) 1 one_ne_zero W hWs hW hbetaLo hMarked
      nativeMu bPhi (globalTau/4) nativeMu_pos hMuCap hbPhi (by positivity)
  have hdeltaNative : g.δ = nativeDriverRate (Fintype.card alpha) := hdelta
  have hheight : 2*g.τ < globalTau := by
    rw [hgtau]
    linarith only [htauCap,hTau]
  refine ⟨g,hmu,hdeltaNative,hheight,?_⟩
  intro T
  obtain ⟨P,hPtau,hPb,hge,hgk,hgv,hgates,SH,hSH,dh,KH,hKH,hsource⟩ := hsubsets T
  refine ⟨P,hge.symm,hPtau.trans hgtau.symm,SH,dh,KH,hKH.le,?_⟩
  intro Q hQM hQ72
  filter_upwards [hsource Q hQM hQ72] with Z hZ
  have hseed : (actualRootParentRow eta heta).character = eta := rfl
  rw [hseed,hEta] at hZ
  simpa only [hmu,hdeltaNative,nativeDriverRate,Cycle153RootHigh.geometryAffineHighDictionaryRate] using hZ.2

end
end OAI.SevenEighths.Cycle153RootInitialHigh

#print axioms OAI.SevenEighths.Cycle153RootInitialHigh.actual_initial_root_high_schedule
