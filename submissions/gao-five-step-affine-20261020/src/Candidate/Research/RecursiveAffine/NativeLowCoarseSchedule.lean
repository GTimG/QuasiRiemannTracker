/- Genuine coarse LOW source, uniformly before moving original subsets/bases.
Copyright (c)2026 Zhongpai Gao. Native coarse bound by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowCoefficient
import Candidate.Research.RecursiveAffine.FiniteSourceUniformization
import Candidate.Research.RecursiveAffine.SourceContextFee

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily Cycle63InitialMass Cycle153SourceSchedule Cycle153SourceUniform
open CenteredMomentNaturalRowSource
variable {alpha : Type}[Fintype alpha]

def nativeLowCoarseExponent (current original : ℕ) : ℝ :=
  4+(39*(4+1)+(4+1)*nativeDriverRate original+(4+1)*1+1)+
    8*(4+1)+3*1+((current:ℝ)+2)*4+2*1+3*(((current:ℝ)+2)*3)*1+4

/-- Keep the ledger-independent original-row coarse estimate. The native
source-to-physical theorem turns this SAME receipt into the LOW coarse
estimate for every regional ledger, including its actual buffered cutoff.
It has no source-energy or count premise. -/
def NativeLowCoarseSubsetAt (T : Finset alpha)(original : ℕ)(Cs K Z : ℝ) : Prop :=
  letI : DecidableEq T:=Classical.decEq _
  MainHighCoarseSideSpec (α:=T) T.card 4 Cs (9/4) (9/4) (2*Real.log (9/4)) 4
    1 (1/4) (nativeDriverRate original) (nativeMu/64) 3 (nativeLowCoarseExponent T.card original) K Z

/-- Derive the physical LOW estimate at the caller's actual regional
ledger and actual subset instance from the SAME unrestricted receipt. -/
theorem native_low_coarse_subset_receipt (T : Finset alpha)(L : Cycle63.AffineLedger)
    (instT : DecidableEq T)(original : ℕ)(Cs K Z : ℝ)
    (source : NativeLowCoarseSubsetAt T original Cs K Z) :
    letI : Cycle63.AffineLedger:=L
    letI : DecidableEq T:=instT
    MainLowCompleteCoarseSpec (α:=T) (Fintype.card T) 4 Cs (9/4) (9/4) (2*Real.log (9/4)) 4
      1 (1/4) (nativeDriverRate original) (nativeMu/64) 3
      (nativeLowCoarseExponent (Fintype.card T) original) K Z :=by
  have hDec : Classical.decEq T=instT:=Subsingleton.elim _ _
  cases hDec
  letI : Cycle63.AffineLedger:=L
  letI : DecidableEq T:=Classical.decEq _
  exact main_low_complete_coarse_spec_of_original (Fintype.card T) 4 Cs (9/4) (9/4)
    (2*Real.log (9/4)) 4 1 (1/4) (nativeDriverRate original) (nativeMu/64) 3
    (nativeLowCoarseExponent (Fintype.card T) original) K Z
    (by simpa only [NativeLowCoarseSubsetAt,Fintype.card_coe] using source)

/-- Invoke the genuine native coarse source for every ORIGINAL subset,
choose all constants before Z, and intersect its true cutoffs at every
actual rebase U≥1/50. This supplies the large-height branch of the real
LOW splice without specializing an eventual theorem to a moving type. -/
theorem eventual_actual_native_low_coarse_sources (eta : Character)(Cs : ℝ)(hCs : 1 ≤ Cs) :
    ∃K : Finset alpha→ℝ,(∀T,0<K T) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ) ≤ U→
        ∀T : Finset alpha,NativeLowCoarseSubsetAt T (Fintype.card alpha) Cs (K T) (Z^U) :=by
  have hsource : ∀T : Finset alpha,∃K : ℝ,0<K ∧
      ∀ᶠY : ℝ in atTop,NativeLowCoarseSubsetAt T (Fintype.card alpha) Cs K Y :=by
    intro T
    letI : DecidableEq T:=Classical.decEq _
    have hxi : nativeMu/64 ≤ (1:ℝ) :=by norm_num [nativeMu,Cycle153.RegionalSchedule.primitiveError]
    have hc:=actual_main_high_original_coarse_side_payment (α:=T) eta 1 (naturalRow eta 1 one_ne_zero) 1 one_ne_zero
      T.card (by simp only [Fintype.card_coe];exact le_rfl)
      4 1 1 1 Cs (9/4) (9/4) (2*Real.log (9/4)) 4 1 (1/4) 1
      (nativeDriverRate (Fintype.card alpha)) (nativeMu/64) 3
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hCs (by norm_num) (by norm_num)
      (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (nativeDriverRate_budgets _).1.le (div_nonneg nativeMu_pos.le (by norm_num)) hxi (by norm_num)
    simpa only [NativeLowCoarseSubsetAt,nativeLowCoarseExponent] using hc
  choose K hK hreceipt using hsource
  exact ⟨K,hK,eventually_all_rebased_sources _ (Filter.eventually_all.mpr hreceipt)⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_native_low_coarse_sources
