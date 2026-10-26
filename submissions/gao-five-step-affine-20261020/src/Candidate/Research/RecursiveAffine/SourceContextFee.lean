/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextFactory
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalLossParameters

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63InitialMass Cycle153Reachable Cycle153.RegionalSchedule

/-- The physical sourcecap is still130. Returned norm caps do not enter
this native driver rate. -/
def nativeDriverRate (N : ℕ) : ℝ :=
  geometryFinalDictionaryRate nativeMu 31 3 4 3 130 (3*((N:ℝ)+2)) N

def nativeSlotLoss (N : ℕ) : ℝ := 2*nativeDriverRate N*31*(N:ℝ)

/-- Post-dictionary shell/multiplicity errors are chosen after Bnorm and
N, before Z and every moving source. This is where a large returned norm
cap is paid, rather than silently substituting physical cap130. -/
def postDictionaryRate (Bnorm : ℝ) (N : ℕ) : ℝ :=
  min (nativeDriverRate N) (nativeMu/(1024*(Bnorm+3*((N:ℝ)+2)+1)))

def postShellCost (Bnorm : ℝ) (N : ℕ) : ℝ :=
  (Bnorm+3*((N:ℝ)+2))*postDictionaryRate Bnorm N

theorem nativeDriverRate_budgets (N : ℕ) :
    0<nativeDriverRate N ∧ nativeDriverRate N≤nativeMu/128 ∧
    nativeSlotLoss N≤nativeMu/32 := by
  have h:=geometry_final_dictionary_budgets nativeMu 31 3 4 3 130 (3*((N:ℝ)+2)) N
    nativeMu_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity)
  rcases h with ⟨hpos,hcommon,hcap,hplain,hlow,hhigh,hslot,hplaincost,hjoined⟩
  exact ⟨hpos,hcap,hslot⟩

theorem postDictionaryRate_budgets {Bnorm : ℝ} (hB : 0≤Bnorm) (N : ℕ) :
    0<postDictionaryRate Bnorm N ∧ postDictionaryRate Bnorm N≤nativeMu/1024 ∧
    postShellCost Bnorm N≤nativeMu/1024 := by
  let rawRate := nativeMu/(1024*(Bnorm+3*((N:ℝ)+2)+1))
  have hp : 0<rawRate := div_pos nativeMu_pos (by positivity)
  have he : rawRate*(1024*(Bnorm+3*((N:ℝ)+2)+1))=nativeMu :=
    div_mul_cancel₀ _ (by positivity)
  have hN : (0:ℝ)≤N := Nat.cast_nonneg N
  have hcap : rawRate≤nativeMu/1024 := by
    nlinarith only [he,hp,hB,hN,mul_nonneg hB hp.le,mul_nonneg hN hp.le]
  have hcost : (Bnorm+3*((N:ℝ)+2))*rawRate≤nativeMu/1024 := by
    nlinarith only [he,hp]
  have hle : postDictionaryRate Bnorm N≤rawRate := min_le_right _ _
  refine ⟨lt_min (nativeDriverRate_budgets N).1 hp,hle.trans hcap,?_⟩
  unfold postShellCost
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hcost

theorem postDictionaryRate_le_native (Bnorm : ℝ) (N : ℕ) :
    postDictionaryRate Bnorm N≤nativeDriverRate N := min_le_left _ _

/-- Build the literal path-fee record from the actual detector deletion
and its actual rounded target. Source padding is the measured native pad;
no fee bound or desired energy bound is an input to this constructor. -/
def scheduledNativeFee (eps : ℝ) (heps : 0<eps) (N : ℕ) (Bnorm : ℝ)
    (modelDeletion nativeDeletion actualDeletion junction sourcePad : ℝ)
    (hmodel : modelDeletion≤nativeDeletion)
    (hdeletion : actualDeletion≤nativeDeletion+localSlotMesh eps) : NativePathFee where
  driverDelta:=nativeDriverRate N
  driverError:=oldLoss eps
  coefficientError:=postDictionaryRate Bnorm N
  shellCost:=postShellCost Bnorm N
  sourcePad:=sourcePad
  slotLoss:=nativeSlotLoss N
  junction:=junction
  actualDeletion:=actualDeletion
  nativeTargetDeletion:=nativeDeletion
  modelDeletion:=modelDeletion
  primeMesh:=localSlotMesh eps
  primeMesh_nonneg:=(localSlotMesh_pos heps).le
  deletion_upper:=hdeletion
  roundingError:=nativeDeletion-modelDeletion
  roundingError_nonneg:=sub_nonneg.mpr hmodel
  target_eq:=by ring

/-- Native driver/detector rates and explicit rounding/support pads pay
the genuine path fee. The hypotheses are the already measured detector
and coordinate bounds, not a fee estimate. It is stronger than the1e-12
budget used by the fixed rational geometry certificates. -/
theorem scheduledNativeFee_budget {eps Bnorm : ℝ} (heps : 0<eps) (hB : 0≤Bnorm)
    (N : ℕ) (modelDeletion nativeDeletion actualDeletion junction sourcePad : ℝ)
    (hmodel : modelDeletion≤nativeDeletion)
    (hdeletion : actualDeletion≤nativeDeletion+localSlotMesh eps)
    (hq0 : 0≤junction) (hq1 : junction≤1)
    (hpad : sourcePad≤1/(10:ℝ)^20)
    (hround : nativeDeletion-modelDeletion≤2200/(gridSize:ℝ)+1/(10:ℝ)^20) :
    (scheduledNativeFee eps heps N Bnorm modelDeletion nativeDeletion actualDeletion junction
      sourcePad hmodel hdeletion).amount≤1/(10:ℝ)^15 := by
  have hd:=nativeDriverRate_budgets N
  have hp:=postDictionaryRate_budgets hB N
  have he:=(oldLoss_bounds eps).2
  have hm:=(localSlotMesh_gates heps).1
  have hm0:=(localSlotMesh_pos heps).le
  have hbase : 0≤nativeDeletion-modelDeletion+2*localSlotMesh eps := by linarith only [hmodel,hm0]
  have ha : junction*(actualDeletion-modelDeletion+localSlotMesh eps)≤
      nativeDeletion-modelDeletion+2*localSlotMesh eps := by
    have h1:=mul_le_mul_of_nonneg_left (by linarith only [hdeletion] :
      actualDeletion-modelDeletion+localSlotMesh eps≤nativeDeletion-modelDeletion+2*localSlotMesh eps) hq0
    have h2:=mul_le_mul_of_nonneg_right hq1 hbase
    linarith only [h1,h2]
  have hcoarse : (scheduledNativeFee eps heps N Bnorm modelDeletion nativeDeletion actualDeletion junction
      sourcePad hmodel hdeletion).amount≤nativeMu+2/(10:ℝ)^20+2202/(gridSize:ℝ) := by
    dsimp only [NativePathFee.amount,scheduledNativeFee]
    have hmu:=nativeMu_pos
    simp only [div_eq_mul_inv] at hd hp he hm hpad hround ⊢
    nlinarith only [hd.2.1,hd.2.2,hp.2.1,hp.2.2,he,hm,ha,hpad,hround,hmu]
  apply hcoarse.trans
  norm_num [nativeMu,primitiveError,gridSize]
end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.nativeDriverRate_budgets
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.postDictionaryRate_budgets
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.scheduledNativeFee_budget
