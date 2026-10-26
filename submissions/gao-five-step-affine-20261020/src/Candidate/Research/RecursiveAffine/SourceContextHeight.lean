/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextFactory

set_option autoImplicit false
set_option maxHeartbeats 250000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily Cycle63InitialMass Cycle153HighProvider

/-- Density degrees belong to the fixed original dictionaries and are
chosen before native source cutoffs. This positive root exponent pays all
of them. Actual HIGH producers are subsequently invoked with τlow no
larger than this exponent and choose2*g.τ<τlow. -/
def rootZeroExponent {I : Type} [Fintype I] (J : I→ℕ) (cap : ℝ) : ℝ :=
  min cap (nativeMu/(1024*((Finset.univ.sup J:ℕ)+1:ℝ)))/2

theorem rootZeroExponent_pos {I : Type} [Fintype I] (J : I→ℕ)
    {cap : ℝ} (hcap : 0<cap) : 0<rootZeroExponent J cap := by
  unfold rootZeroExponent
  exact div_pos (lt_min hcap (div_pos nativeMu_pos (by positivity))) (by norm_num)

/-- The SAME original height exponent pays every fixed density degree;
it is not selected again after a moving source or retained family. -/
theorem rootZeroExponent_density {I : Type} [Fintype I] (J : I→ℕ)
    {cap : ℝ} (hcap : 0<cap) (i : I) :
    rootZeroExponent J cap≤cap ∧
    2*rootZeroExponent J cap*((J i:ℝ)+1)≤nativeMu/1024 := by
  have hp:=rootZeroExponent_pos J hcap
  have hcap' : 2*rootZeroExponent J cap≤cap := by
    dsimp only [rootZeroExponent]
    linarith only [min_le_left cap (nativeMu/(1024*((Finset.univ.sup J:ℕ)+1:ℝ)))]
  have hrate : 2*rootZeroExponent J cap≤nativeMu/(1024*((Finset.univ.sup J:ℕ)+1:ℝ)) := by
    dsimp only [rootZeroExponent]
    linarith only [min_le_right cap (nativeMu/(1024*((Finset.univ.sup J:ℕ)+1:ℝ)))]
  have hJ : (J i:ℝ)≤(Finset.univ.sup J:ℕ) := by exact_mod_cast Finset.le_sup (Finset.mem_univ i)
  have hden : 0<1024*((Finset.univ.sup J:ℕ)+1:ℝ) := by positivity
  have hprod := (le_div_iff₀ hden).mp hrate
  refine ⟨by linarith only [hcap',hp],?_⟩
  nlinarith only [hprod,hJ,hp,mul_le_mul_of_nonneg_left hJ hp.le]

/-- Exact presentation exponent at a rebased actual child. Tz is the
same real bound Z^τRoot, and its local exponent is divided by U. -/
theorem source_zero_height_rebase {Z U tau : ℝ} (hZ : 1<Z) (hU : 0<U) :
    (Z^U)^(tau/U)=Z^tau := by
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  congr 1
  field_simp [ne_of_gt hU]

/-- This is the direction required by the actual HIGH provider:
τT>=τlow. It does not try to put the zero height below g.τ. -/
theorem local_presentation_height {U tau tauLow : ℝ}
    (hU : 0<U) (hU1 : U≤1) (htau : 0≤tau) (hlow : tauLow≤tau) :
    tauLow≤tau/U := by
  apply hlow.trans
  rw [le_div_iff₀ hU]
  exact mul_le_of_le_one_right htau hU1

/-- Construct the literal native prefix presentation with the exact
unchanged global zero height, at every actual child base. -/
theorem actual_rebased_high_presentation {Base : Type} (base : Base→Character)
    {Z U tau tauLow Bmask bPhi : ℝ} (hZ : 1<Z) (hU : 0<U) (hU1 : U≤1)
    (htau : 0≤tau) (hlow : tauLow≤tau)
    (s : CenteredMomentEnergyState.NaturalState (Z^U) Bmask bPhi)
    (P : PrefixHighPresentation base s.character s.puncture) :
    tauLow≤tau/U ∧ PrefixHighPresented base (tau/U) (Z^U) s P.mult (Z^tau) := by
  refine ⟨local_presentation_height hU hU1 htau hlow,?_,?_⟩
  · rw [source_zero_height_rebase hZ hU]
    exact ⟨le_rfl,le_rfl⟩
  · exact ⟨P,rfl⟩

/-- A finite family of actual producer cutoffs lies below half of the
already fixed root height exponent. One later threshold absorbs all
constant buffer-height factors uniformly over moving child units. -/
theorem eventually_actual_high_buffer_height {I : Type} [Fintype I]
    (g : I→GeometryAffineLowSchedule) (tau : ℝ) (hcut : ∀i,2*(g i).τ<tau) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,0<U → U≤1 →
      ∀i,6*(Z^U)^((g i).τ)*(Z^U)^((g i).τ)≤Z^tau := by
  filter_upwards [Filter.eventually_all.2 (fun i=>
    (tendsto_rpow_atTop (by linarith only [hcut i] : 0<tau-2*(g i).τ)).eventually
      (eventually_ge_atTop (6:ℝ))),eventually_gt_atTop (1:ℝ)] with Z h hZ
  refine ⟨hZ,?_⟩
  intro U hU hU1 i
  have hz:=zero_lt_one.trans hZ
  have hle : (Z^U)^((g i).τ)≤Z^((g i).τ) := by
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le
      (mul_le_of_le_one_left (g i).τ_pos.le hU1)
  have hmajor : 6*(Z^U)^((g i).τ)*(Z^U)^((g i).τ)≤6*Z^((g i).τ)*Z^((g i).τ) := by
    gcongr
  apply hmajor.trans
  calc
    6*Z^((g i).τ)*Z^((g i).τ)≤Z^(tau-2*(g i).τ)*Z^((g i).τ)*Z^((g i).τ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h i)
        (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)
    _=Z^tau := by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      ring
/-- The actual polynomial in the common zero height is absorbed in the
fixed original base. Its degree is chosen from the original dictionary
count before the source schedule is made. -/
theorem eventually_root_height_density {I : Type} [Fintype I] (J : I→ℕ)
    {cap : ℝ} (hcap : 0<cap) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀i,
      (1+Z^(rootZeroExponent J cap))^(J i)≤Z^(nativeMu/1024) := by
  have ht:=rootZeroExponent_pos J hcap
  filter_upwards [(tendsto_rpow_atTop ht).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hx hZ
  refine ⟨hZ,?_⟩
  intro i
  let x:=Z^(rootZeroExponent J cap)
  have hx0 : 0≤x := Real.rpow_nonneg (zero_le_one.trans hZ.le) _
  have hquad : 1+x≤x^2 := by change 2≤x at hx;nlinarith only [hx]
  have hpower (k : ℕ) : x^k=Z^(rootZeroExponent J cap*(k:ℝ)) := by
    dsimp only [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ.le)]
  calc
    (1+Z^(rootZeroExponent J cap))^(J i)≤(x^2)^(J i) :=
      pow_le_pow_left₀ (by positivity) hquad _
    _=Z^(rootZeroExponent J cap*(2*(J i:ℝ))) := by
      rw [←pow_mul,hpower]
      push_cast
      rfl
    _≤Z^(nativeMu/1024) := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hb:=(rootZeroExponent_density J hcap i).2
      nlinarith only [hb,ht]

end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.rootZeroExponent_density
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.actual_rebased_high_presentation
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.eventually_actual_high_buffer_height

#print axioms OAI.SevenEighths.Cycle153SourceSchedule.eventually_root_height_density
