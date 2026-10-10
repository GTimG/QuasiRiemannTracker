import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
import WeightedQRH.MomentDetectorPlainMarkedState
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O


def weighted_delta (D:WeightedQRH.MomentData):ℝ := D.t/4
def weighted_stageError (D:WeightedQRH.MomentData):ℝ := D.t/4
def weighted_kappaPlain (_D:WeightedQRH.MomentData):ℝ := 3/4

theorem weighted_fixed_parameters (D:WeightedQRH.MomentData):
    0<weighted_delta D ∧ weighted_delta D ≤ 1/4 ∧ 0<weighted_stageError D ∧
    weighted_delta D+weighted_stageError D ≤ D.t ∧ 3/4 ≤ weighted_kappaPlain D ∧ 0<weighted_kappaPlain D := by
  dsimp [weighted_delta,weighted_stageError,weighted_kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma weighted_source_base_gt_one (_D:WeightedQRH.MomentData)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ) ≤ d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma weighted_witness_length_cap (D:WeightedQRH.MomentData):
    1/2+75*D.ε ≤ (23/40:ℝ) := by linarith [D.epsilon_small]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem weighted_actual_fiber_lengths (D:WeightedQRH.MomentData)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1<U):
    0 ≤ F.m ∧ F.m ≤ 1/2+75*D.ε ∧ F.m ≤ 23/40 ∧
    1 ≤ U^F.m ∧ U^F.m ≤ U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (weighted_witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m ≤ 1 by linarith)
  · exact weighted_plain_length_eq F hU

lemma weighted_width_bands (D:WeightedQRH.MomentData)(m:ℝ)(hm:m ≤ 23/40):
    1 ≤ 1+weighted_delta D ∧ 1+weighted_delta D ≤ 2 ∧
    1 ≤ max 1 (2*m)+weighted_delta D ∧ max 1 (2*m)+weighted_delta D ≤ 2 := by
  have hδ:0<weighted_delta D:=(weighted_fixed_parameters D).1
  have hd:weighted_delta D ≤ 1/4:=(weighted_fixed_parameters D).2.1
  have hmax:max 1 (2*m) ≤ 23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem weighted_unmarked_state_admission (D:WeightedQRH.MomentData)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0 ≤ (Φ x).re)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^(weighted_delta D)):
    let s:=state F η Q Φ bΦ (weighted_delta D) hU.le (weighted_fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=weighted_initialKeep η Q ∧
    s.width=max 1 (2*F.m)+weighted_delta D ∧ 1 ≤ s.width ∧ s.width ≤ 2 ∧
    1 ≤ U^F.m ∧ U^F.m ≤ U ∧ 2*length U (U^F.m) ≤ s.width := by
  dsimp only
  have hf:=weighted_actual_fiber_lengths D F hU
  have hw:=weighted_width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (weighted_delta D) hU.le (weighted_fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+weighted_delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (weighted_fixed_parameters D).1.le)

theorem weighted_source_label_fixed_allowance (D:WeightedQRH.MomentData)
    (S:ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ) ≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ (Z^d)^(weighted_delta D) :=
  weighted_source_label_modulus_eventually S η (weighted_delta D) (weighted_fixed_parameters D).1

lemma weighted_final_exponent_budget (D:WeightedQRH.MomentData)(base:ℝ):
    base+weighted_delta D+weighted_stageError D ≤ base+D.t := by
  linarith [(weighted_fixed_parameters D).2.2.2.1]

end SevenEighths.CenteredMomentDetectorPlainMomentParameters

end

end OAI
