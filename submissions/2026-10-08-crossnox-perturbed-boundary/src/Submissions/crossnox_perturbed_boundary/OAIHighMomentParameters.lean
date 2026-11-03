/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentParameters.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighMomentMarkedState
import Submissions.crossnox_perturbed_boundary.OAIHighMomentGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.PerturbedMomentTransport
open CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {gap:ℝ}

def delta (D:Parameters.PerturbedHighData gap):ℝ := D.small/4
def stageError (D:Parameters.PerturbedHighData gap):ℝ := D.small/4

theorem fixed_parameters (D:Parameters.PerturbedHighData gap):
    0<delta D ∧ delta D≤1/4 ∧ 0<stageError D ∧
    delta D+stageError D≤D.small ∧ 3/4≤kappaPlain D ∧ 0<kappaPlain D := by
  have hsmall := D.small_pos
  dsimp [delta, stageError, kappaPlain]
  refine ⟨by positivity, ?_, by positivity, ?_, le_rfl, by norm_num⟩ <;>
    linarith [D.small_cap]

lemma source_base_gt_one (_D:Parameters.PerturbedHighData gap)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (D:Parameters.PerturbedHighData gap):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths (D:Parameters.PerturbedHighData gap)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1<U):
    0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact plain_length_eq F hU

lemma width_bands (D:Parameters.PerturbedHighData gap)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0<delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission (D:Parameters.PerturbedHighData gap)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain D)*(∑s:selected,F.widths s.val)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact marked_capacity F hU selected (kappaPlain D) (delta D) (fixed_parameters D).1.le hcap

theorem admit_selected_source_moment (D : Parameters.PerturbedHighData gap)
    (F : Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (hU : 1 < U) (selected : Finset (Fin D.N)) (d : ℝ) (hd : 0 < d)
    (hwidth : ∀ j, F.widths j = D.ell j / d)
    (hcapacity : 2 * d * F.m + (9 / 2 : ℝ) * (∑ j ∈ selected, D.ell j) ≤ d) :
    length U (U^F.m) + length U (U^F.m) +
      6 * kappaPlain D * (∑ j : selected, F.widths j.val) ≤ 1 + delta D := by
  have hnormalized := (normalize_selected_moment_capacity D selected d F.m hd).mpr hcapacity
  have hmarked : 2 * F.m + 6 * kappaPlain D * (∑ j ∈ selected, F.widths j) ≤ 1 := by
    simpa only [hwidth] using hnormalized
  exact marked_capacity F hU selected (kappaPlain D) (delta D)
    (fixed_parameters D).1.le hmarked

theorem unmarked_state_admission (D:Parameters.PerturbedHighData gap)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ 2*length U (U^F.m)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters D).1.le)

theorem source_label_fixed_allowance (D:Parameters.PerturbedHighData gap)
    (S:ProbeFinalAssembly.PerturbedSourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  ProbeFinalAssembly.perturbed_source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget (D:Parameters.PerturbedHighData gap)(base:ℝ):
    base+delta D+stageError D≤base+D.small := by
  linarith [(fixed_parameters D).2.2.2.1]

lemma fine_slot_widths (D : Parameters.PerturbedHighData gap)
    (mesh : ℝ) (hfine : ∀ j, D.ell j ≤ mesh / 200)
    (d : ℝ) (hd : (1 / 200 : ℝ) ≤ d) (j : Fin D.N) :
    0 < D.ell j / d ∧ D.ell j / d ≤ mesh := by
  have hdpos : 0 < d := by linarith
  have hmesh : 0 < mesh := by
    have := (D.slots_bounds j).1
    have := hfine j
    linarith
  refine ⟨div_pos (D.slots_bounds j).1 hdpos, (div_le_iff₀ hdpos).mpr ?_⟩
  nlinarith [hfine j]

end SevenEighths.PerturbedMomentTransport

end

end OAI
