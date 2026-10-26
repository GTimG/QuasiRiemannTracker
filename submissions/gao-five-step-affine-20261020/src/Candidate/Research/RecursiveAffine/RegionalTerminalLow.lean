/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalLowSelectedAt
import Candidate.Research.RecursiveAffine.FixedStages
import Candidate.Research.RecursiveAffine.RegionalFiniteFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAtStateProof

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153Terminal
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentAllocatedRayDictionary Cycle63InitialMass
local instance affineParentBranchesSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost

variable {α : Type} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
local instance regionalLowSelectedFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


open Cycle153RegionalLow Cycle153 ProbePhysical

variable [Cycle63.AffineLedger] in
/-- The genuine old-region source bound is exactly the zero-return LOW interface. -/
theorem terminal_low_zero_return
    (W : ℝ→ℂ)(hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Mcap Lslot Cs : ℝ)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z 28 2 → O → ℝ → Prop)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})(Z : ℝ)
    (hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Rc Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRc : Rc ≤ 20)(hRcap : (R.absNorm:ℝ) ≤ Z^Rc)(hMrow : 0 ≤ Mrow)(hMrow1 : Mrow ≤ 1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+g.μ/16)
    (hAdm : Adm 1 (frequencyLoss Z 32 (g.μ/64)+g.μ/8) (g.μ/64))
    (height mesh : ℝ)(hw : ∀j,0 ≤ w j)
    (hwL : ∀j,w j ≤ Lslot)
    (hwr : ∀j,w j/31 ≤ 1)(hmesh : 0 ≤ mesh)(hwm : ∀j,w j ≤ mesh)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (hzslot : Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.B)
    (hclosed : GeometryAffineLowSelectedSpec (α:=α) M H hH W hbeta g Mcap Lslot Cs Adm Presented
      Sp degreeAll Kall η₀ Q hQM hQ72 Z) :
    RegionalLowSelectedAt (α:=α) M H hH W hbeta g Mcap Lslot Cs Adm Presented Sp degreeAll Kall
      η₀ Q hQM hQ72 Z 0 hZ s p caps θ w σ freq hm R seed Rc Mrow hR hseed hRc hRcap hMrow hMrow1
      hfit hAdm height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi hzslot haff := by
  unfold RegionalLowSelectedAt
  intro Label inst
  have h := @hclosed hZ s p caps θ w σ freq hm R seed Rc Mrow hR hseed hRc hRcap hMrow hMrow1
    hfit hAdm height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi hzslot haff Label inst
  simpa only [add_zero,mul_assoc,mul_comm,mul_left_comm] using h

variable [Cycle63.AffineLedger] [Cycle63.AffineLedger.DeletesIntoOldRegion] in
/-- The terminal LOW source is fully discharged by the native old-region
moment, uniformly before the moving source state and coefficients. -/
theorem terminal_actual_low_spec
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (g : GeometryAffineLowSchedule)
    (Cs : ℝ) (hCs : 1 ≤ Cs) (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) :
    ∃(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ),0 ≤ Kall ∧
      ∀ᶠZ : ℝ in atTop,GeometryAffineLowSelectedSpec (α:=α) M H hH W hbeta g 2
        (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) Sp degreeAll Kall η₀ Q hQM hQ72 Z := by
  have hrow5 : LowSelectedPaidAt M H hH g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
      (fun _ _ _=>True) lowGeometryExponent (fun _ _ _ _ _ _=>True) :=
    lowSelectedPaidAt_of_columns M H hH actual_selected_low_paid_columns_closed g 2 _
      (by norm_num) le_rfl le_rfl
  have hgate : LowBinGate lowGeometryExponent 6 := actual_geometry_low_bin_gate.mono (by norm_num)
  let k:=actual_affine_low_selected_payment (α:=α) M H hH hgate W hWs hW hbeta g 2 _
    (by norm_num) le_rfl hrow5 Cs hCs
    (fixedSourcePrincipal fixedBadPrimes Parameters.fixed_bad_primes_prime) 1
    (fixedSourceNaturalRow fixedBadPrimes Parameters.fixed_bad_primes_prime (Finset.Subset.refl _))
    1 one_ne_zero η₀ Q hQM hQ0 hQt hQ72
  exact ⟨k.2.1,k.1,k.2.2.2.1,k.2.2.2.2.down.1.le,k.2.2.2.2.down.2.mono (fun _ h=>h.2)⟩

/-- The last finite step has the original LOW region and no recursive daughter. -/
theorem terminal_regional_deletes_old (P : RegionalPosition) (h : P.Facts FixedStages.stage4) :
    @Cycle63.AffineLedger.DeletesIntoOldRegion (regionalLedger FixedStages.stage4 P h) := by
  letI : Cycle63.AffineLedger := regionalLedger FixedStages.stage4 P h
  constructor
  · change (4499/6000:ℝ)=Cycle63.Optimization.slotPrice
    norm_num [Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound]
  · change (1/1:ℝ)=1
    norm_num

end
end OAI.SevenEighths.Cycle153Terminal
#print axioms OAI.SevenEighths.Cycle153Terminal.terminal_low_zero_return
#print axioms OAI.SevenEighths.Cycle153Terminal.terminal_regional_deletes_old

#print axioms OAI.SevenEighths.Cycle153Terminal.terminal_actual_low_spec
