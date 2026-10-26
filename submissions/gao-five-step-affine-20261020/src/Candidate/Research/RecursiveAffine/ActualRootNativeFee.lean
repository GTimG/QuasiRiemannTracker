/- Literal bare-root native fees, without a fictitious reachable parent.
Copyright (c) 2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualNodeNativeFee
import Candidate.Research.RecursiveAffine.NativeRootStep

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open Cycle63InitialMass Cycle153SourceSchedule Cycle153.RegionalSchedule Cycle153RootStep

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}

/-- The original root physical pad, at the literal global base and the
actual ambient source cardinality. -/
def actualRootSourcePad (C : SourceContext (α:=alpha) M H)(s : Input alpha) : ℝ :=
  2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+
    Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂)

/-- Bare-root source fee. Its density junction is the genuine q0, and its
model target is the exact root cell deletion; only the explicit detector
surcharge1e−20 separates that model target from the native detector. -/
def actualRootNativeFee (C : SourceContext (α:=alpha) M H)(s : Input alpha)
    (eps : ℝ)(budget : ℕ)(Rdel : Finset alpha)
    (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+C.slotMesh) : NativePathFee where
  driverDelta:=nativeDriverRate budget
  driverError:=oldLoss eps
  coefficientError:=postDictionaryRate C.Bnorm budget
  shellCost:=130*postDictionaryRate C.Bnorm budget
  sourcePad:=actualRootSourcePad C s
  slotLoss:=2*nativeDriverRate budget*31*(Fintype.card alpha:ℝ)
  junction:=Cycle153Geometry.Coordinates.q0
  actualDeletion:=∑i∈Rdel,C.originalWeight i
  nativeTargetDeletion:=rootDetectorDeletion C.originalWeight
  modelDeletion:=rootSourceDeletion C.originalWeight
  primeMesh:=C.slotMesh
  primeMesh_nonneg:=C.slotMesh_pos.le
  deletion_upper:=hdeleted
  roundingError:=1/(10:ℝ)^20
  roundingError_nonneg:=by positivity
  target_eq:=by unfold rootDetectorDeletion;norm_num

/-- Exact fee identity for the actual selected raw root edge. No larger
ambient error is inserted into its exponent. -/
theorem actual_root_native_fee_amount (s : Input alpha)(eps : ℝ)(budget : ℕ)(Rdel : Finset alpha)
    (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+C.slotMesh) :
    (actualRootNativeFee C s eps budget Rdel hdeleted).amount=
      3*nativeDriverRate budget+oldLoss eps+postDictionaryRate C.Bnorm budget+
        130*postDictionaryRate C.Bnorm budget+actualRootSourcePad C s+
        2*nativeDriverRate budget*31*(Fintype.card alpha:ℝ)+
        Cycle153Geometry.Coordinates.q0*((∑i∈Rdel,C.originalWeight i)-rootSourceDeletion C.originalWeight+C.slotMesh) :=rfl

/-- The genuine large-base pad threshold and chosen source schedule pay
the exact bare-root fee. Both the finite geometry pad and fee estimates
are conclusions, uniformly before every moving source and detector. -/
theorem eventually_actual_root_native_fee_budget (eps : ℝ)(heps : 0<eps)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(s : Input alpha),C.globalBase=Z→
      s.b₁=(9/4:ℝ)→s.b₂=(9/4:ℝ)→C.slotMesh ≤ localSlotMesh eps→Fintype.card alpha ≤ budget→
    ∀(Rdel : Finset alpha)
      (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+C.slotMesh),
      Real.logb C.globalBase 128+actualRootSourcePad C s ≤ 1/(10:ℝ)^20 ∧
      (actualRootNativeFee C s eps budget Rdel hdeleted).amount ≤ 1/(10:ℝ)^15 :=by
  filter_upwards [eventually_actual_native_pad budget] with Z hz
  refine ⟨hz.1,?_⟩
  intro C s hbase hb1 hb2 hmesh hcard Rdel hdeleted
  have hpadFull:=hz.2 1 (by norm_num) (Fintype.card alpha) hcard (9/4) s.b₁ s.b₂
    (by norm_num) le_rfl hb1.le hb2.le
  rw [Real.rpow_one,←hbase] at hpadFull
  have hg : 0 ≤ 252/(gridSize:ℝ) :=by positivity
  have hfinite : Real.logb C.globalBase 128+actualRootSourcePad C s ≤ 1/(10:ℝ)^20 :=by
    dsimp only [actualRootSourcePad]
    linarith only [hpadFull,hg]
  have hlog128 : 0 ≤ Real.logb C.globalBase 128:=Real.logb_nonneg C.globalBase_gt_one (by norm_num)
  have hpad : actualRootSourcePad C s ≤ 1/(10:ℝ)^20 :=by linarith only [hfinite,hlog128]
  have hmodel : rootSourceDeletion C.originalWeight ≤ rootDetectorDeletion C.originalWeight :=by
    unfold rootDetectorDeletion
    linarith
  have hdeleted' : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+localSlotMesh eps :=by
    linarith only [hdeleted,hmesh]
  have hround : rootDetectorDeletion C.originalWeight-rootSourceDeletion C.originalWeight ≤
      2200/(gridSize:ℝ)+1/(10:ℝ)^20 :=by
    unfold rootDetectorDeletion
    have hh : 0 ≤ 2200/(gridSize:ℝ) :=by positivity
    norm_num only
    linarith only [hh]
  have hq : 0 ≤ Cycle153Geometry.Coordinates.q0 ∧ Cycle153Geometry.Coordinates.q0 ≤ 1 :=by
    norm_num [Cycle153Geometry.Coordinates.q0]
  let larger:=scheduledNativeFee eps heps budget C.Bnorm (rootSourceDeletion C.originalWeight)
    (rootDetectorDeletion C.originalWeight) (∑i∈Rdel,C.originalWeight i) Cycle153Geometry.Coordinates.q0
    (actualRootSourcePad C s) hmodel hdeleted'
  have hbudget:=scheduledNativeFee_budget heps C.normCap_nonneg budget _ _ _ _ _ hmodel hdeleted' hq.1 hq.2 hpad hround
  have hrate:=postDictionaryRate_budgets C.normCap_nonneg budget
  have hB : (130:ℝ) ≤ C.Bnorm:=by linarith only [C.normCap_large]
  have hshell : 130*postDictionaryRate C.Bnorm budget ≤ postShellCost C.Bnorm budget :=by
    dsimp only [postShellCost]
    have hN : (0:ℝ) ≤ budget:=Nat.cast_nonneg budget
    nlinarith only [hrate.1,mul_nonneg hN hrate.1.le,mul_nonneg (sub_nonneg.mpr hB) hrate.1.le]
  have hslot : 2*nativeDriverRate budget*31*(Fintype.card alpha:ℝ) ≤ nativeSlotLoss budget :=by
    have hc : (Fintype.card alpha:ℝ) ≤ budget:=by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_left hc (by have hp:=(nativeDriverRate_budgets budget).1;positivity)
  have hcompare : (actualRootNativeFee C s eps budget Rdel hdeleted).amount ≤ larger.amount :=by
    dsimp only [actualRootNativeFee,larger,scheduledNativeFee,NativePathFee.amount]
    have hm:=mul_le_mul_of_nonneg_left hmesh hq.1
    linarith only [hshell,hslot,hm]
  exact ⟨hfinite,hcompare.trans hbudget⟩

/-- A real proper detector's coverage and the actual root slot window
also pay the coarse remaining coefficient at the SAME literal fee. -/
theorem actual_root_native_fee_remaining
    (s : Input alpha)(eps : ℝ)(budget : ℕ)(Rdel : Finset alpha)
    (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+C.slotMesh)
    (hcover : rootDetectorDeletion C.originalWeight ≤ ∑i∈Rdel,C.originalWeight i)
    (hwindow : @Cycle63.AffineLedger.PlainWindow Cycle153.Root.rootLedger
      (CenteredMomentEnergyBands.length C.globalBase s.X₁)
      (CenteredMomentEnergyBands.length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (hbudget : (actualRootNativeFee C s eps budget Rdel hdeleted).amount ≤ 1/(10:ℝ)^15) :
    (actualRootNativeFee C s eps budget Rdel hdeleted).junction*
      (actualRootNativeFee C s eps budget Rdel hdeleted).modelDeletion+
      (actualRootNativeFee C s eps budget Rdel hdeleted).amount ≤ 2 :=by
  have hsub : (∑i∈Rdel,C.originalWeight i) ≤ ∑i,C.originalWeight i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>C.originalWeight_nonneg i)
  have hD : rootSourceDeletion C.originalWeight ≤ 1 :=by
    have hslots:=hwindow.slots_le.trans (@Cycle63.AffineLedger.slotTop_le_one Cycle153.Root.rootLedger)
    unfold rootDetectorDeletion at hcover
    norm_num only at hcover
    linarith only [hcover,hsub,hslots]
  have hq : 0 ≤ Cycle153Geometry.Coordinates.q0 ∧ Cycle153Geometry.Coordinates.q0 ≤ 1 :=by
    norm_num [Cycle153Geometry.Coordinates.q0]
  have hmul:=mul_le_mul_of_nonneg_left hD hq.1
  change Cycle153Geometry.Coordinates.q0*rootSourceDeletion C.originalWeight+_ ≤ 2
  nlinarith only [hmul,hq.2,hbudget]
/-- Full root fee consumer: the true finite pad, fine fee and proper
source's coarse remainder are produced together, with no fee premise. -/
theorem eventually_actual_root_native_fee (eps : ℝ)(heps : 0<eps)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(s : Input alpha),C.globalBase=Z→
      s.b₁=(9/4:ℝ)→s.b₂=(9/4:ℝ)→C.slotMesh ≤ localSlotMesh eps→Fintype.card alpha ≤ budget→
    ∀(Rdel : Finset alpha)
      (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+C.slotMesh),
      Real.logb C.globalBase 128+actualRootSourcePad C s ≤ 1/(10:ℝ)^20 ∧
      (actualRootNativeFee C s eps budget Rdel hdeleted).amount ≤ 1/(10:ℝ)^15 ∧
      ((rootDetectorDeletion C.originalWeight ≤ ∑i∈Rdel,C.originalWeight i)→
      (@Cycle63.AffineLedger.PlainWindow Cycle153.Root.rootLedger
        (CenteredMomentEnergyBands.length C.globalBase s.X₁)
        (CenteredMomentEnergyBands.length C.globalBase s.X₂) (∑i,C.originalWeight i))→
      (actualRootNativeFee C s eps budget Rdel hdeleted).junction*
        (actualRootNativeFee C s eps budget Rdel hdeleted).modelDeletion+
        (actualRootNativeFee C s eps budget Rdel hdeleted).amount ≤ 2) :=by
  filter_upwards [eventually_actual_root_native_fee_budget (alpha:=alpha) (M:=M) (H:=H) eps heps budget] with Z hz
  refine ⟨hz.1,?_⟩
  intro C s hbase hb1 hb2 hmesh hcard Rdel hdeleted
  have hb:=hz.2 C s hbase hb1 hb2 hmesh hcard Rdel hdeleted
  refine ⟨hb.1,hb.2,?_⟩
  intro hcover hwindow
  exact actual_root_native_fee_remaining s eps budget Rdel hdeleted hcover hwindow hb.2

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.eventually_actual_root_native_fee_budget
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_native_fee_amount

#print axioms OAI.SevenEighths.Cycle153Reachable.eventually_actual_root_native_fee
