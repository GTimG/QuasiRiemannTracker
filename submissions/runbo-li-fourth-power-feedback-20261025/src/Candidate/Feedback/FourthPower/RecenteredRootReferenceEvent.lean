/- Copyright (c) 2026 Sil. Apache-2.0.
One event pays fixed conductor, support and dimension factors for the
kept reference. All moving rectangles follow this event.
-/
import Candidate.Feedback.FourthPower.RecenteredRootReferenceDictionary

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RecenteredRootReferenceEvent
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSecondHeightFamily MixedFirstReferenceEnergy
open RepairedRootParameters

def conductorUpper (η:Character)(bΦ Z:ℝ) : ℝ :=
  max 1 (conductorFactor η fixedBadMask 1*(bΦ*Z))

def Event (N:ℕ)(η:Character)(bΦ ε Z:ℝ) : Prop :=
  1<Z ∧ 16≤Z ∧ ((9/4+4:ℝ)*(9/4)*2^N≤Z^(omegaLoss ε)) ∧
    bΦ*Z≤Z^(1+omegaLoss ε) ∧ conductorUpper η bΦ Z≤Z^(1+2*omegaLoss ε)

theorem eventual_event (N:ℕ)(η:Character)(bΦ ε:ℝ)(hε:0<ε) :
    ∀ᶠ Z:ℝ in atTop,Event N η bΦ ε Z := by
  have hω:0<omegaLoss ε := (omega_spec ε hε).1
  have hp (A:ℝ) : ∀ᶠ Z:ℝ in atTop,A≤Z^(omegaLoss ε) :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hω)) A
  filter_upwards [eventually_ge_atTop (16:ℝ),hp ((9/4+4:ℝ)*(9/4)*2^N),
    hp bΦ,hp (conductorFactor η fixedBadMask 1*bΦ)] with Z hZ16 hdim hb hc
  have hZ:1<Z := by linarith
  have hz:0<Z := zero_lt_one.trans hZ
  have hb':bΦ*Z≤Z^(1+omegaLoss ε) := by
    calc
      _≤Z^(omegaLoss ε)*Z := mul_le_mul_of_nonneg_right hb hz.le
      _=_ := by rw [Real.rpow_add hz,Real.rpow_one];ring
  have hc':conductorFactor η fixedBadMask 1*(bΦ*Z)≤Z^(1+omegaLoss ε) := by
    calc
      _=(conductorFactor η fixedBadMask 1*bΦ)*Z := by ring
      _≤Z^(omegaLoss ε)*Z := mul_le_mul_of_nonneg_right hc hz.le
      _=_ := by rw [Real.rpow_add hz,Real.rpow_one];ring
  have hunit:1≤Z^(1+omegaLoss ε) := Real.one_le_rpow hZ.le (by linarith)
  have hupper:conductorUpper η bΦ Z≤Z^(1+omegaLoss ε) := max_le hunit hc'
  refine ⟨hZ,hZ16,hdim,hb',?_⟩
  exact hupper.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

theorem event_dimension {N n:ℕ}{η:Character}{bΦ ε Z:ℝ}(hn:n≤N)
    (h:Event N η bΦ ε Z) : ((9/4+4:ℝ)*(9/4)*2^n)≤Z^(omegaLoss ε) :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hn) (by norm_num)).trans h.2.2.1

theorem conductor_upper_gates {N:ℕ}{η:Character}{bΦ ε Z Lcap:ℝ}(hε:0<ε)
    (hLcap:8≤Lcap)(h:Event N η bΦ ε Z) :
    1≤conductorUpper η bΦ Z ∧ conductorUpper η bΦ Z≤Z^(Lcap+8) ∧
      conductorUpper η bΦ Z≤Z^((1+omegaLoss ε)+omegaLoss ε) ∧
      conductorFactor η fixedBadMask 1*(bΦ*Z)≤conductorUpper η bΦ Z := by
  have hω:omegaLoss ε≤1/10000000000 := (omega_spec ε hε).2.2.2
  refine ⟨le_max_left _ _,?_,?_,le_max_right _ _⟩
  · exact h.2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le h.1.le (by linarith))
  · convert h.2.2.2.2 using 1 <;> congr 1 <;> ring

theorem reference_total_cap {ε P S:ℝ}(hε:0<ε)(hf:RepairedRootParameters.Face P S)(hh:NeedsCentering ε P S) :
    (1+omegaLoss ε)+
      (centeredExponent ε P S+((1+omegaLoss ε)+omegaLoss ε)/2+S+2*omegaLoss ε)≤4 := by
  have hg:=(reference_gates hε hf hh).2.1
  have hω:omegaLoss ε≤1/10000000000 := (omega_spec ε hε).2.2.2
  linarith

end
end Candidate.Feedback.FourthPower.RecenteredRootReferenceEvent
