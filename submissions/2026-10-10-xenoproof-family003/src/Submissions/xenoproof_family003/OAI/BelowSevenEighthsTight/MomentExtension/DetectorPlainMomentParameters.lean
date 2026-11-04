/- UNVERIFIED moment parameter extension at the rational capacity baseline. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedHighData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState

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

variable {Δ L margin mesh:ℝ}

def delta_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh):ℝ := D.t/4
def stageError_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh):ℝ := D.t/4
def kappaPlain_retuned (_D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh):ℝ := _root_.BelowSevenEighthsTight.kappaRat+2*Δ

theorem fixed_parameters_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh):
    0<delta_retuned D ∧ delta_retuned D≤1/4 ∧ 0<stageError_retuned D ∧
    delta_retuned D+stageError_retuned D≤D.t ∧ 13/18<kappaPlain_retuned D ∧ 0<kappaPlain_retuned D := by
  have hΔ:0<Δ:=by linarith [D.t_pos,D.t_delta]
  have hκ0 : (13/18:ℝ)<_root_.BelowSevenEighthsTight.kappaRat := by
    norm_num [_root_.BelowSevenEighthsTight.kappaRat]
  dsimp [delta_retuned,stageError_retuned,kappaPlain_retuned]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma source_base_gt_one_retuned (_D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

lemma original_width_bounds_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)(d:ℝ)
    (hd:(1/200:ℝ)≤d)(s:Fin D.N):0<D.ell s/d ∧ D.ell s/d≤D.t := by
  have hdpos:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds s).1 hdpos,(div_le_iff₀ hdpos).mpr ?_⟩
  have hs: D.ell s≤(1/200:ℝ)*D.t:=(D.slots_bounds s).2.2
  nlinarith [D.t_pos]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1<U):
    0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap_retuned D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact plain_length_eq F hU

theorem batch_fiber_parameters_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d)
    (B:Batch M H Label (Fin D.N) (Z^d) a D.ε tstar T heightAllowance i)
    (hwidth:B.widths=(fun s=>D.ell s/d))
    (bin label J K)(hne:(B.fiberRows bin label J K).Nonempty):
    let F:=B.fiber bin label J K hne;
    1<Z^d ∧ 0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤(Z^d)^F.m ∧ (Z^d)^F.m≤Z^d ∧ length (Z^d) ((Z^d)^F.m)=F.m ∧
    (∀s,0<F.widths s ∧ F.widths s≤D.t) ∧
    (∀selected:Finset (Fin D.N),∀s:selected,0<F.widths s.val ∧ F.widths s.val≤D.t) := by
  dsimp only
  have hU:=source_base_gt_one_retuned D Z d hZ hd
  have hf:=actual_fiber_lengths_retuned D (B.fiber bin label J K hne) hU
  have hw:∀s,0<(B.fiber bin label J K hne).widths s ∧
      (B.fiber bin label J K hne).widths s≤D.t:=by
    intro s
    change 0<B.widths s ∧ B.widths s≤D.t
    rw [hwidth]
    exact original_width_bounds_retuned D d hd s
  exact ⟨hU,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    hw,fun _ s=>hw s.val⟩

lemma width_bands_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)(m:ℝ)(hm:m≤23/40):
    1≤1+delta_retuned D ∧ 1+delta_retuned D≤2 ∧
    1≤max 1 (2*m)+delta_retuned D ∧ max 1 (2*m)+delta_retuned D≤2 := by
  have hδ:0<delta_retuned D:=(fixed_parameters_retuned D).1
  have hd:delta_retuned D≤1/4:=(fixed_parameters_retuned D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta_retuned D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain_retuned D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta_retuned D) hU.le (fixed_parameters_retuned D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta_retuned D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain_retuned D)*(∑s:selected,F.widths s.val)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths_retuned D F hU
  have hw:=width_bands_retuned D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact marked_capacity F hU selected (kappaPlain_retuned D) (delta_retuned D) (fixed_parameters_retuned D).1.le hcap

theorem unmarked_state_admission_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta_retuned D)):
    let s:=state F η Q Φ bΦ (delta_retuned D) hU.le (fixed_parameters_retuned D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta_retuned D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ 2*length U (U^F.m)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths_retuned D F hU
  have hw:=width_bands_retuned D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta_retuned D) hU.le (fixed_parameters_retuned D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta_retuned D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters_retuned D).1.le)

lemma final_exponent_budget_retuned (D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ L margin mesh)(base:ℝ):
    base+delta_retuned D+stageError_retuned D≤base+D.t := by
  linarith [(fixed_parameters_retuned D).2.2.2.1]

theorem actual_capacity_identity (β : ℝ)
    (D : _root_.BelowSevenEighthsTight.Parameters.RetunedHighData
      (β-_root_.BelowSevenEighthsTight.sigmaRat) L margin mesh) :
    kappaPlain_retuned D=2*β-1 := by
  have h := _root_.BelowSevenEighthsTight.rational_parameters.2.1
  dsimp only [kappaPlain_retuned]
  rw [h]
  ring

end SevenEighths.CenteredMomentDetectorPlainMomentParameters

end

end OAI

#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.fixed_parameters_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.source_base_gt_one_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.witness_length_cap_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.original_width_bounds_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.actual_fiber_lengths_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.batch_fiber_parameters_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.width_bands_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.marked_state_admission_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.unmarked_state_admission_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.final_exponent_budget_retuned
#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters.actual_capacity_identity
