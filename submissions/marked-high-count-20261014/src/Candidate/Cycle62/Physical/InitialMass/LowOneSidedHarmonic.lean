import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle62InitialMass.LowOneSided
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentCommonHarmonicMass CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentWholeDivisorShell
local notation "O" => ActualEisensteinCubic.O

/-- One-sided reciprocal weight for the two separate joint Cauchy energies. -/
def sideWeight (second : Bool) (v : Label) : ℝ :=
  1/((if second then v.1.2 else v.1.1).absNorm:ℝ)

lemma one_sided_shell_scalar (e Y x y d : ℝ) (he : 0<e) (hx : 0<x) (hy : 0<y)
    (hd : 0<d) (hmin : min x y≤d) (hY : min x y≤Y) :
    (2*min x y)^(1+e)/d≤2^(1+e)*Y^e := by
  have hm : 0<min x y := lt_min hx hy
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  apply (div_le_iff₀ hd).mpr
  calc
    _≤2^(1+e)*(d*Y^e) := mul_le_mul_of_nonneg_left
      (mul_le_mul hmin hp (by positivity) hd.le) (by positivity)
    _=_ := by ring

/-- The same Rankin shell count used by the symmetric harmonic estimate
also controls either reciprocal norm separately. -/
theorem one_sided_shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀second : Bool, ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0<T₁ → 0<T₂ → min T₁ T₂≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,sideWeight second v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro second s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0<Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  let d := if second then T₂ else T₁
  have hsq : 0<d := by cases second <;> assumption
  have hmin : min T₁ T₂≤d := by
    cases second
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/d := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      cases second
      · exact (hshell v hv).1
      · exact (hshell v hv).2.2.1
    _ = (S.card:ℝ)/d := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/d :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/d) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (one_sided_shell_scalar e Y T₁ T₂ d he hT₁ hT₂ hsq hmin hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

theorem one_sided_polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀second : Bool, ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,sideWeight second v)≤C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := one_sided_shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro second Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,sideWeight second v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound second s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

theorem one_sided_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀second : Bool, ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,sideWeight second v)≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := one_sided_polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro second Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound second Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end
end OAI.SevenEighths.Cycle62InitialMass.LowOneSided
#print axioms OAI.SevenEighths.Cycle62InitialMass.LowOneSided.one_sided_shell_scalar
#print axioms OAI.SevenEighths.Cycle62InitialMass.LowOneSided.one_sided_shell_bound
#print axioms OAI.SevenEighths.Cycle62InitialMass.LowOneSided.one_sided_polynomial_cap_log_bound
#print axioms OAI.SevenEighths.Cycle62InitialMass.LowOneSided.one_sided_harmonic_mass
