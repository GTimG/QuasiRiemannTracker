/- Copyright (c) 2026 Sil. Apache-2.0.
Homogeneous profile bounds for the restored source. Each final ordinary
profile control is squared once; no source or energy estimate is assumed.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedSourceSideSupply

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedSourceProfiles
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedOriginalTail MixedFirstProfileEnvelope RepairedSourceSideSupply
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem control_mono (p : Profiles a b) {S T : Finset (ℕ×ℕ)} (h : S ⊆ T) :
    p.control S ≤ p.control T := by
  have hm (W : 𝓢(ℝ,ℂ)) : sourceControl S W ≤ sourceControl T W :=
    Seminorm.le_def.mp (Finset.sup_mono h) W
  exact mul_le_mul (hm _) (hm _) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem root_height (t V : ℝ) (hV : 0 ≤ V) :
    1 ≤ 1+|t|+V ∧ height t V t t ≤ 3*(1+|t|+V) ∧ height 0 0 t t ≤ 2*(1+|t|+V) := by
  unfold height
  simp only [Real.norm_eq_abs,abs_zero]
  constructor
  · linarith [abs_nonneg t]
  · constructor <;> linarith [abs_nonneg t]

/-- The zero/tail profile amplitude follows from source seminorms and
the actual fixed marked bound; it is not an energy premise. -/
theorem profileCap_sq_le_amplitude (s : Source ι a b) (N : ℕ) (hcard : Fintype.card ι ≤ N)
    (Kslot : ℝ) (hKslot : 1 ≤ Kslot) (hM : ∀i,s.M i ≤ Kslot)
    (t₀ V : ℝ) (hV : 0 ≤ V) (J : ℕ) (control : Finset (ℕ×ℕ)) (h00 : (0,0)∈control)
    (Cside : ℝ) (hCside : 1 ≤ Cside) :
    (profileCap s)^2 ≤ (4*Kslot^(2*N))*amplitude s t₀ V J control Cside := by
  let P := sourceControl control s.W₁*sourceControl control s.W₂
  have hP : 0 ≤ P := mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hc (W : 𝓢(ℝ,ℂ)) : supControl W ≤ sourceControl control W :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.singleton_subset_iff.mpr h00)) W
  have hplain : supControl s.W₁*supControl s.W₂ ≤ P :=
    mul_le_mul (hc _) (hc _) (supControl_nonneg _) (sourceControl_nonneg _ _)
  have hmarked : (∏i,s.M i) ≤ Kslot^N := by
    calc
      _ ≤ ∏_i:ι,Kslot := Finset.prod_le_prod₀
        (fun i _ => zero_le_one.trans (s.hM i)) (fun i _ => hM i)
      _ = Kslot^(Fintype.card ι) := by simp only [Finset.prod_const,Finset.card_univ]
      _ ≤ _ := pow_le_pow_right₀ hKslot hcard
  have hmarked0 : 0 ≤ ∏i,s.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.hM i))
  have hcap : profileCap s ≤ 2*P*Kslot^N := by
    calc
      _ = 2*(supControl s.W₁*supControl s.W₂)*(∏i,s.M i) := by unfold profileCap;ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hplain (by norm_num)) hmarked hmarked0
        (mul_nonneg (by norm_num) hP)
  have hh : 1 ≤ height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hcost : 1 ≤ Cside*(height t₀ V s.t₁ s.t₂)^J :=
    one_le_mul_of_one_le_of_one_le hCside (one_le_pow₀ hh)
  have hA : P^2 ≤ amplitude s t₀ V J control Cside := by
    have he := le_mul_of_one_le_left (sq_nonneg P) hcost
    convert he using 1 <;> (try simp only [amplitude,P]) <;> ring
  have hpow : (Kslot^N)^2=Kslot^(2*N) := by rw [←pow_mul,Nat.mul_comm]
  calc
    _ ≤ (2*P*Kslot^N)^2 := pow_le_pow_left₀ (profileCap_nonneg s) hcap 2
    _ = (4*Kslot^(2*N))*P^2 := by rw [mul_pow,mul_pow,hpow];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

theorem actual_amplitude_bound (s : Source ι a b) (p : Profiles a b)
    (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
    (t V : ℝ) (hV : 0 ≤ V) (ht₁ : s.t₁=t) (ht₂ : s.t₂=t)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) (hCside : 0 ≤ Cside) :
    amplitude s t V J control Cside ≤
      (Cside*3^J)*(p.control control)^2*(1+|t|+V)^J := by
  have hh0 : 0 ≤ height t V t t := by unfold height;positivity
  have hp := pow_le_pow_left₀ hh0 (root_height t V hV).2.1 J
  unfold amplitude
  rw [hW₁,hW₂,ht₁,ht₂]
  have he := mul_le_mul_of_nonneg_left hp (mul_nonneg hCside (sq_nonneg (p.control control)))
  rw [mul_pow] at he
  convert he using 1 <;> (try simp only [Profiles.control]) <;> ring

theorem reference_height_bound (p : Profiles a b) (t V : ℝ) (hV : 0 ≤ V)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0 ≤ C) :
    C*(p.control control)^2*(height 0 0 t t)^J ≤
      (C*2^J)*(p.control control)^2*(1+|t|+V)^J := by
  have hh0 : 0 ≤ height 0 0 t t := by unfold height;positivity
  have hp := pow_le_pow_left₀ hh0 (root_height t V hV).2.2 J
  have he := mul_le_mul_of_nonneg_left hp (mul_nonneg hC (sq_nonneg (p.control control)))
  rw [mul_pow] at he
  convert he using 1 <;> ring

theorem profile_budget_mono (p : Profiles a b) (t V Z e0 e : ℝ)
    (hV : 0 ≤ V) (hZ : 1 ≤ Z) (he : e0 ≤ e)
    (J0 J : ℕ) (hJ : J0 ≤ J) (S0 S : Finset (ℕ×ℕ)) (hS : S0 ⊆ S) :
    (p.control S0)^2*(1+|t|+V)^J0*Z^e0 ≤ (p.control S)^2*(1+|t|+V)^J*Z^e := by
  have hp := pow_le_pow_left₀ (p.control_nonneg S0) (control_mono p hS) 2
  have hh := pow_le_pow_right₀ (root_height t V hV).1 hJ
  have hz := Real.rpow_le_rpow_of_exponent_le hZ he
  exact mul_le_mul (mul_le_mul hp hh (pow_nonneg (zero_le_one.trans (root_height t V hV).1) _)
    (sq_nonneg _)) hz (Real.rpow_nonneg (zero_le_one.trans hZ) _) (mul_nonneg (sq_nonneg _) (by positivity))

end
end Candidate.FourthPower.RepairedSourceProfiles
