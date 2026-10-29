/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.InitialSelectedBound
import Candidate.Local.Qrh.JointDetector.Contraction
import Candidate.Local.Qrh.JointDetector.ActiveReflection
import Candidate.Local.Qrh.JointDetector.SelectedSlotData

/-! Actual reflected-envelope improvement for the selected norm. Descendant
bounds are explicit induction hypotheses; reflection itself is proved. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

/-- Exact reflected power, with both residual divisor powers visible. -/
theorem reflected_power_identity (L B D R H q δ : ℝ)
    (hL : 0 < L) (hB : 0 < B) (hD : 0 < D) (hR : 0 < R) (hH : 0 < H) :
    (L*D/(B*R))*(B/D)^q*((4*B^2*R/(L*D^2))*H)^δ =
      (4*H)^δ*B^(q+2*δ-1)*L^(1-δ)*D^(1-q-2*δ)*R^(δ-1) := by
  rw [show 1-q-2*δ = 1-(q+2*δ) by ring]
  rw [Real.rpow_sub hB (q+2*δ) 1,Real.rpow_add hB q (2*δ),
    Real.rpow_sub hL 1 δ,Real.rpow_sub hD 1 (q+2*δ),Real.rpow_add hD q (2*δ),
    Real.rpow_sub hR δ 1]
  simp only [Real.rpow_one]
  rw [Real.div_rpow hB.le hD.le,
    Real.mul_rpow (by positivity : 0 ≤ 4*B^2*R/(L*D^2)) hH.le,
    Real.div_rpow (by positivity : 0 ≤ 4*B^2*R) (by positivity : 0 ≤ L*D^2),
    Real.mul_rpow (by positivity : 0 ≤ 4*B^2) hR.le,
    Real.mul_rpow (by norm_num : (0 : ℝ)≤4) (sq_nonneg B),
    Real.mul_rpow hL.le (sq_nonneg D),Real.mul_rpow (by norm_num : (0 : ℝ)≤4) hH.le,
    ← Real.rpow_natCast_mul hB.le 2 δ, ← Real.rpow_natCast_mul hD.le 2 δ]
  norm_num only [Nat.cast_ofNat]
  ring

/-- Both the shared gcd and source-mask/bad-sector factors have favorable
powers throughout the closed slope interval above one half. -/
theorem reflected_power_le (L B D R H q δ : ℝ)
    (hL : 0 < L) (hB : 0 < B) (hD : 1 ≤ D) (hR : 1 ≤ R) (hH : 1 ≤ H)
    (hq : 0 ≤ q) (hδ : 1/2 ≤ δ) (hδ1 : δ ≤ 1) :
    (L*D/(B*R))*(B/D)^q*((4*B^2*R/(L*D^2))*H)^δ ≤
      4*H*B^(q+2*δ-1)*L^(1-δ) := by
  have hD0 : 0 < D := by linarith
  have hR0 : 0 < R := by linarith
  have hH0 : 0 < H := by linarith
  rw [reflected_power_identity L B D R H q δ hL hB hD0 hR0 hH0]
  have hd : D^(1-q-2*δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hD (by linarith)
  have hr : R^(δ-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hh : (4*H)^δ ≤ 4*H := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ 4*H by linarith) hδ1
  calc
    _ ≤ (4*H)*B^(q+2*δ-1)*L^(1-δ)*1*1 := by gcongr
    _ = _ := by ring

/-- The complete reflected scalar envelope in the long-source range. -/
theorem reflected_envelope_le (L B D R H K q δ : ℝ)
    (hL : 0 < L) (hB : 0 < B) (hBL : B ≤ L) (hD : 1 ≤ D)
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hδ : 1/2 ≤ δ) (hδ1 : δ ≤ 1) :
    let Y := (4*B^2*R/(L*D^2))*H
    L/R + (L*D/(B*R))*(K*(Y+(B/D)^q*Y^δ)) ≤
      5*K*H*(L+B^(q+2*δ-1)*L^(1-δ)) := by
  dsimp only
  have hD0 : 0 < D := by linarith
  have hR0 : 0 < R := by linarith
  have hH0 : 0 < H := by linarith
  have hK0 : 0 < K := by linarith
  have hlin : (L*D/(B*R))*((4*B^2*R/(L*D^2))*H) = 4*B*H/D := by field_simp
  have hp := reflected_power_le L B D R H q δ hL hB hD hR hH hq hδ hδ1
  have hp' := mul_le_mul_of_nonneg_left hp hK0.le
  have hlin' : K*((L*D/(B*R))*((4*B^2*R/(L*D^2))*H)) ≤ K*(4*L*H) := by
    rw [hlin]
    apply mul_le_mul_of_nonneg_left _ hK0.le
    exact (div_le_self (by positivity) hD).trans (by gcongr)
  have hbase : L/R ≤ L := div_le_self hL.le hR
  have hKH : 1 ≤ K*H := one_le_mul_of_one_le_of_one_le hK hH
  have hmass := mul_le_mul_of_nonneg_right hKH hL.le
  have hother : 0 ≤ B^(q+2*δ-1)*L^(1-δ) := by positivity
  nlinarith

/-- Apply the actual descendant operator envelope to the precise finite
reflected maximum. The hypothesis is the norm bound at the PREVIOUS
induction stage, for the very same inherited quotient rows. -/
theorem simpleReflectionProfile_improve (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (L B H K q δ : ℝ)
    (hL : 1 ≤ L) (hB : 0 < B) (hBL : B ≤ L) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hq : 0 ≤ q) (hδ : 1/2 ≤ δ) (hδ1 : δ ≤ 1)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ 2*B)
    (hdesc : ∀ k ∈ BadFrequencySectors.boundedKeys L,
      ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      let Y := reflectedFrequencyCutoff L B H D e k
      selectedNorm (selectedQuotientRows F D) (selectedFrequencyPool (reflectionFrequencies Y) Y) ≤
        K*(Y+(B/(Ideal.absNorm D : ℝ))^q*Y^δ)) :
    simpleReflectionProfile F L B H ≤ 5*K*H*(L+B^(q+2*δ-1)*L^(1-δ)) := by
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  apply simpleReflectionProfile_le_of_modes F L B H _ (by positivity)
  intro k hk D hD e he
  have hd := selectedGcd_spec F hF (2*B) hN D hD
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hh => hd.1.1 (Ideal.absNorm_eq_zero_iff.mp hh))
  have hR := (reflectedSourceRatio_range F hF L B hL hN D hD e he k hk).1
  have hfactor : 0 ≤ L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k) := by positivity
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hdesc k hk D hD e he) hfactor)).trans
  exact reflected_envelope_le L B (Ideal.absNorm D : ℝ) (reflectedSourceRatio e k) H K q δ
    hL0 hB hBL hDN hR hH hK hq hδ hδ1


theorem activeReflectionProfile_improve (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (L B H K q δ : ℝ)
    (hL : 1 ≤ L) (hB : 0 < B) (hBL : B ≤ L) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hq : 0 ≤ q) (hδ : 1/2 ≤ δ) (hδ1 : δ ≤ 1)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ 2*B)
    (hdesc : ∀ k ∈ activeInputKeys L,
      ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      let Y := reflectedFrequencyCutoff L B H D e k
      selectedNorm (selectedQuotientRows F D) (selectedFrequencyPool (reflectionFrequencies Y) Y) ≤
        K*(Y+(B/(Ideal.absNorm D : ℝ))^q*Y^δ)) :
    activeReflectionProfile F L B H ≤ 5*K*H*(L+B^(q+2*δ-1)*L^(1-δ)) := by
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  apply activeReflectionProfile_le_of_modes F L B H _ (by positivity)
  intro k hk D hD e he
  have hd := selectedGcd_spec F hF (2*B) hN D hD
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hh => hd.1.1 (Ideal.absNorm_eq_zero_iff.mp hh))
  have hR := (reflectedSourceRatio_range F hF L B hL hN D hD e he k (Finset.mem_filter.mp hk).1).1
  have hfactor : 0 ≤ L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k) := by positivity
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hdesc k hk D hD e he) hfactor)).trans
  exact reflected_envelope_le L B (Ideal.absNorm D : ℝ) (reflectedSourceRatio e k) H K q δ
    hL0 hB hBL hDN hR hH hK hq hδ hδ1


/-- One genuine reflection improvement, uniform in the slope and exponent.
The descendant envelope is the induction input; all analytic reflection,
zero modes, masks and tails have already been proved. -/
theorem squarefree_reflection_improvement (P loss : ℝ) (hP : 0 ≤ P) (hloss : 0 < loss) :
    ∃ C Z₀ s : ℝ, 0 < C ∧ 0 < s ∧ s ≤ 1 ∧
      ∀ (Z L B K q δ : ℝ) (F S : Finset (Ideal O)),
      Z₀ ≤ Z → 1 ≤ L → L ≤ Z^P → 1 ≤ B → B ≤ Z^P → B ≤ L →
      1 ≤ K → 0 ≤ q → 1/2 ≤ δ → δ ≤ 1 →
      (∀ I ∈ F, Admissible I) →
      (∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
        (Ideal.span {(36 : O)} : Ideal O)) →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      (∀ k ∈ activeInputKeys L,
        ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
        let Y := reflectedFrequencyCutoff L B (Z^s) D e k
        selectedNorm (selectedQuotientRows F D) (selectedFrequencyPool (reflectionFrequencies Y) Y) ≤
          K*(Y+(B/(Ideal.absNorm D : ℝ))^q*Y^δ)) →
      selectedNorm (F.image primaryGenerator) S ≤
        C*K*Z^loss*(L+B^(q+2*δ-1)*L^(1-δ)) := by
  obtain ⟨C,Z₀,s,hC,hs,hs1,hsloss,hreflection⟩ := squarefree_active_uniform_reflection P (loss/2) hP (by positivity)
  refine ⟨5*C,max Z₀ 1,s,by positivity,hs,hs1,?_⟩
  intro Z L B K q δ F S hZ hL hLU hB hBU hBL hK hq hδ hδ1 hF hmod hN hS hdesc
  have hz1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hK0 : 0 < K := by linarith
  have hprofile := activeReflectionProfile_improve F hF L B (Z^s) K q δ hL (by linarith)
    hBL (Real.one_le_rpow hz1 hs.le) hK hq hδ hδ1 (fun I hI => (hN I hI).2) hdesc
  calc
    _ ≤ C*Z^(loss/2)*activeReflectionProfile F L B (Z^s) :=
      hreflection Z L B F S ((le_max_left _ _).trans hZ) hL hLU hB hBU hF hmod hN hS
    _ ≤ C*Z^(loss/2)*(5*K*Z^s*(L+B^(q+2*δ-1)*L^(1-δ))) :=
      mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ = (5*C)*K*Z^(loss/2+s)*(L+B^(q+2*δ-1)*L^(1-δ)) := by rw [Real.rpow_add hz]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by positivity)


/-- The long envelope is at most twice its linear term above the exact
crossing; this is uniform in the real exponent. -/
theorem long_envelope_above_crossing (B Y c δ : ℝ) (hB : 0 < B) (hY : 0 < Y)
    (hδ : 0 < δ) (hcross : B^(c/δ) ≤ Y) :
    Y+B^c*Y^(1-δ) ≤ 2*Y := by
  have hp : B^c ≤ Y^δ := by
    calc
      _ = (B^(c/δ))^δ := by rw [← Real.rpow_mul hB.le,div_mul_cancel₀ _ hδ.ne']
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) hcross hδ.le
  have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hY.le (1-δ))
  have he : Y^δ*Y^(1-δ) = Y := by rw [← Real.rpow_add hY]; convert Real.rpow_one Y using 1 <;> ring
  rw [he] at hh
  linarith

/-- The exact scalar cost of a prefix word crossing. Its overshoot costs
only the single prescribed ambient mesh, independent of word degree. -/
theorem amplified_long_envelope_le (Z L B Y c δ mesh : ℝ)
    (hZ : 1 ≤ Z) (hL : 0 < L) (hB : 0 < B) (hY : 0 < Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ mesh)
    (hcross : B^(c/δ) ≤ Y) (hupper : Y ≤ Z^mesh*B^(c/δ)) :
    (Y+B^c*Y^(1-δ))/(Y/L)^δ ≤
      2*Z^mesh*B^(Contraction.ratio δ*c)*L^δ := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hden : 0 < (Y/L)^δ := Real.rpow_pos_of_pos (div_pos hY hL) _
  have hid : Y/(Y/L)^δ = L^δ*Y^(1-δ) := by
    rw [Real.div_rpow hY.le hL.le,Real.rpow_sub hY 1 δ,Real.rpow_one]
    field_simp
  have hscale : Y^(1-δ) ≤ Z^mesh*B^(Contraction.ratio δ*c) := by
    calc
      _ ≤ (Z^mesh*B^(c/δ))^(1-δ) :=
        Real.rpow_le_rpow hY.le hupper (by linarith)
      _ = Z^(mesh*(1-δ))*B^((c/δ)*(1-δ)) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hB.le _),
          ← Real.rpow_mul hz.le, ← Real.rpow_mul hB.le]
      _ ≤ Z^mesh*B^((c/δ)*(1-δ)) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)) (Real.rpow_nonneg hB.le _)
      _ = _ := by congr 1; congr 1; unfold Contraction.ratio; ring
  calc
    _ ≤ (2*Y)/(Y/L)^δ := div_le_div_of_nonneg_right
      (long_envelope_above_crossing B Y c δ hB hY hδ hcross) hden.le
    _ = 2*(L^δ*Y^(1-δ)) := by rw [mul_div_assoc,hid]
    _ ≤ 2*(L^δ*(Z^mesh*B^(Contraction.ratio δ*c))) := by gcongr
    _ = _ := by ring


/-- The actual selected-slot descriptor survives every shared-row quotient
with exactly the same coefficient-mass bound. -/
theorem selectedSlotData_quotient_selects {N : ℕ} (d : SelectedSlotData N)
    (F : Finset (Ideal O)) (D : Ideal O) (Z : ℝ)
    (hselect : d.Selects Z (F.image primaryGenerator)) :
    (d.quotient (primaryGenerator D)).Selects Z (selectedQuotientRows F D) := by
  apply SelectedSlotData.quotient_selects hselect
  intro z hz
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hz
  have hi := Finset.mem_filter.mp hI
  apply Finset.mem_image.mpr
  refine ⟨I,hi.1,?_⟩
  rw [← primaryGenerator_mul,idealQuotient_mul hi.2]

theorem descendantIdealFamily_primary_rows (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) :
    (descendantIdealFamily F D).image primaryGenerator = selectedQuotientRows F D := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hI
    rw [primaryGenerator_span r (selectedQuotientRows_spec F hF D ⟨r,hr⟩).1
      (selectedQuotientRows_spec F hF D ⟨r,hr⟩).2.1]
    exact hr
  · intro z hz
    apply Finset.mem_image.mpr
    refine ⟨Ideal.span {z},Finset.mem_image.mpr ⟨z,hz,rfl⟩,?_⟩
    exact primaryGenerator_span z (selectedQuotientRows_spec F hF D ⟨z,hz⟩).1
      (selectedQuotientRows_spec F hF D ⟨z,hz⟩).2.1

/-- Every amplification crossing stays below the cube of its own row
radius; the source cap therefore does not grow exponentially with depth. -/
theorem contraction_exponent_range (δ : ℝ) (n : ℕ) (hδ : 1/2 < δ) (hδ1 : δ ≤ 1) :
    δ ≤ Contraction.exponent δ n ∧ Contraction.exponent δ n ≤ 1+δ ∧
      Contraction.exponent δ n/δ ≤ 3 := by
  have hd : 0 < δ := by linarith
  have hr0 := Contraction.ratio_nonneg hd hδ1
  have hr1 := (Contraction.ratio_lt_one hδ).le
  have hp0 : 0 ≤ Contraction.ratio δ^n := pow_nonneg hr0 n
  have hp1 : Contraction.ratio δ^n ≤ 1 := pow_le_one₀ hr0 hr1
  rw [Contraction.exponent_eq δ hd.ne' n]
  refine ⟨by linarith,by linarith,?_⟩
  apply (div_le_iff₀ hd).mpr
  linarith

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.squarefree_reflection_improvement
#print axioms Qrh.JointDetector.selectedSlotData_quotient_selects
#print axioms Qrh.JointDetector.amplified_long_envelope_le
