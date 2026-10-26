/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalRawLowSelectedAt
import Candidate.Research.RecursiveAffine.NativeRootLowNormalization

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
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
open Cycle153Reachable
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
local instance rootRawParentBranchesSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost

variable {α : Type} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
local instance nativeRootRawLowFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable [Cycle63.AffineLedger] in
/-- EACH actual root source receipt is paid by the genuine native
whole-family count. Normalize its raw AtState power once to obtain the
literal root LOW return. The OLD price comparison remains explicit, and
the dynamic bin/profile/height control is retained outside the fixed
coefficient. No root envelope or fictitious width-one node is used. -/
theorem root_low_selected_of_actual_raw_source
    (W : ℝ→ℂ)(hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Mcap Lslot Cs : ℝ)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z 28 2 → O → ℝ → Prop)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})(Z amp driverError Kreturn Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (C : SourceContext (α:=α) M H)
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
    (hbase : C.globalBase=Z)(hdriver : 0 ≤ driverError)(hKall : 0 ≤ Kall)
    (hcount : ∀receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      Kreturn*receipt.family.value ≤ Z)
    (hsource : RegionalRawLowSelectedAt M H hH W hbeta g Mcap Lslot Cs Adm Presented Sp degreeAll Kall
      η₀ Q hQM hQ72 Z (1+3*g.δ-amp+driverError) Kreturn
      (NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes) (fun receipt=>receipt.family.value)
      hZ s p caps θ w σ freq hm R seed Rc Mrow hR hseed hRc hRcap hMrow hMrow1
      hfit hAdm height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi hzslot haff) :
    RegionalLowSelectedAt M H hH W hbeta g Mcap Lslot Cs Adm Presented Sp degreeAll Kall
      η₀ Q hQM hQ72 Z (Z^(amp-3*g.δ))
      hZ s p caps θ w σ freq hm R seed Rc Mrow hR hseed hRc hRcap hMrow hMrow1
      hfit hAdm height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi hzslot haff := by
  intro Label inst reflected second bin t firstIndex
  dsimp only
  intro hamp0 hamp homega htarget hf₁ hinj hfirstproj χ₀ m hm₀ hml hm₂ Ψ t₀ u
  obtain ⟨hP,hPN,hPNc,raw⟩:=@hsource Label inst reflected second bin t firstIndex
    hamp0 hamp homega htarget hf₁ hinj hfirstproj χ₀ m hm₀ hml hm₂ Ψ t₀ u
  refine ⟨hP,hPN,hPNc,?_⟩
  intro left₁ u₀ unit₁ Tz hleft hu₀ hunits hpresented
  obtain ⟨actual,rawOld,hOld,hraw⟩:=raw left₁ u₀ unit₁ Tz hleft hu₀ hunits hpresented
  have hcontrol : 0 ≤ (p.control Sp)^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
      (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll := by
    have hf:=(geometry_high_factor_pos reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin
      (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
    positivity
  have hcount' : Kreturn*actual.family.value ≤ C.globalBase := (hcount actual).trans_eq hbase.symm
  have hpow (x : ℝ) : C.globalBase^x=Z^x :=congrArg (fun z : ℝ=>z^x) hbase
  have hraw' := hraw
  conv at hraw' => lhs;arg 1;rw [←hpow _]
  conv at hraw' => rhs;arg 1;arg 2;rw [←hpow _]
  have he:=actual_root_low_raw_normalization actual amp g.δ driverError _ rawOld
    Kall Kreturn _ _ hdriver hKall hcontrol hcount'
    (by simpa only [add_assoc] using hOld) hraw'
  simpa only [hpow,mul_assoc] using he

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.root_low_selected_of_actual_raw_source
