/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FiveColourNorm
import Candidate.Local.Qrh.JointDetector.RadialBilinear

/-!
# One common Mellin kernel for the actual five-colour pivot swap

The coordinates x(v,u), y(w,q) are the FULL residual radical coordinates of
that row. The same radial ratio R, source coordinate z(I), and Mellin kernel
are used for every higher tuple. The row phases enter their own arbitrary
dual vectors; the source phase is a common source weight. All original
coprime selectors and natural cross-colour zeros remain in the finite form.
-/
namespace Qrh.JointDetector.FiveColourMellin
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI EisensteinSchwartzPoisson
open FiveColourNorm
local notation "O" => ActualEisensteinCubic.O

section Swap
variable {VL VR : Type*} [Fintype VL] [Fintype VR]
variable (EL : VL → Finset O) (ER : VR → Finset O) (S : Finset (Ideal O))
variable (A : Fibre EL → ℂ) (B : Fibre ER → ℂ)
variable (FL : O → VR → ℂ) (FR : O → VL → ℂ)
variable (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
variable (x : Fibre EL → ℝ) (y : Fibre ER → ℝ) (z : S → ℝ)

/-- Five finite indices in the order of the original nonrectangular swap. -/
abbrev SwapIndex := Σ v : VL, Σ w : VR, S × EL v × ER w

def swapCoefficient (j : SwapIndex EL ER S) : ℂ :=
  H j.1 j.2.1*weight j.1 j.2.1 j.2.2.1*
    if IsCoprime (Ideal.span {j.2.2.2.1.val}) (Ideal.span {j.2.2.2.2.val}) then
      (selectedMatrix (EL j.1) S j.2.2.1 j.2.2.2.1*(A ⟨j.1,j.2.2.2.1⟩*star (FL j.2.2.2.1.val j.2.1)))*
      (star (selectedMatrix (ER j.2.1) S j.2.2.1 j.2.2.2.2)*(B ⟨j.2.1,j.2.2.2.2⟩*FR j.2.2.2.2.val j.1)) else 0

/-- The ACTUAL radial Fourier kernel, before any positive estimate. -/
def radialCoprimeSwap (W : 𝓢(ℝ,ℂ)) (R : ℝ) : ℂ :=
  ∑ j : SwapIndex EL ER S, swapCoefficient EL ER S A B FL FR H weight j*
    paperRadialFourier W (R*z j.2.2.1/(x ⟨j.1,j.2.2.2.1⟩*y ⟨j.2.1,j.2.2.2.2⟩))

/-- The common t phase preserves the original fibre coefficient mass. -/
def phaseVector {F : Type*} (a : F → ℂ) (coord : F → ℝ) (t : ℝ) : F → ℂ :=
  fun u => a u*FourierBridge.logPhase t (-Real.log (coord u))

def phaseWeight (t : ℝ) (v : VL) (w : VR) (I : S) : ℂ :=
  weight v w I*FourierBridge.logPhase t (Real.log (z I))

theorem phaseVector_norm {F : Type*} (a : F → ℂ) (coord : F → ℝ) (t : ℝ) (u : F) :
    ‖phaseVector a coord t u‖ = ‖a u‖ := by
  simp only [phaseVector,norm_mul,FourierBridge.logPhase_norm,mul_one]

theorem phaseWeight_norm_le (hweight : ∀ v w I, ‖weight v w I‖ ≤ 1) (t : ℝ) :
    ∀ v w I, ‖phaseWeight S weight z t v w I‖ ≤ 1 := by
  intro v w I
  simpa only [phaseWeight,norm_mul,FourierBridge.logPhase_norm,mul_one] using hweight v w I

/-- Exact finite Fubini: ONE common Fourier phase gives the same coprime
swap, with own full-radical coordinates multiplying the two dual arrays. -/
theorem swap_phase_sum (t : ℝ) :
    (∑ j : SwapIndex EL ER S, swapCoefficient EL ER S A B FL FR H weight j*
      radialLogPhase t (x ⟨j.1,j.2.2.2.1⟩) (y ⟨j.2.1,j.2.2.2.2⟩) (z j.2.2.1)) =
    coprimeSwap EL ER S (phaseVector A x t) (phaseVector B y t) FL FR H (phaseWeight S weight z t) := by
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,coprimeSwap,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only [swapCoefficient,phaseVector,phaseWeight,radialLogPhase]
  split_ifs <;> simp_all <;> ring

/-- The radial kernel is integrated with a single b_R, before summing any
higher tuple or ordinary source. No family of unrelated L1 kernels occurs. -/
theorem radialCoprimeSwap_eq_integral (W b : 𝓢(ℝ,ℂ)) (R : ℝ)
    (hx : ∀ u, x u ∈ Set.Icc (1 : ℝ) 2) (hy : ∀ u, y u ∈ Set.Icc (1 : ℝ) 2)
    (hz : ∀ I, z I ∈ Set.Icc (1 : ℝ) 2)
    (hi : Integrable (fun t : ℝ => ‖b t‖) volume)
    (hsep : ∀ x y z : ℝ, x ∈ Set.Icc (1 : ℝ) 2 → y ∈ Set.Icc (1 : ℝ) 2 →
      z ∈ Set.Icc (1 : ℝ) 2 → paperRadialFourier W (R*z/(x*y)) =
        ∫ t : ℝ, radialLogPhase t x y z*b t) :
    radialCoprimeSwap EL ER S A B FL FR H weight x y z W R =
      ∫ t : ℝ, b t*coprimeSwap EL ER S (phaseVector A x t) (phaseVector B y t) FL FR H
        (phaseWeight S weight z t) := by
  unfold radialCoprimeSwap
  rw [finite_radial_integral W b R (swapCoefficient EL ER S A B FL FR H weight)
    (fun j => x ⟨j.1,j.2.2.2.1⟩) (fun j => y ⟨j.2.1,j.2.2.2.2⟩) (fun j => z j.2.2.1)
    (fun j => hx _) (fun j => hy _) (fun j => hz _) hi hsep]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by dsimp only; rw [swap_phase_sum]
/-- Source-feature orientation produced by the ACTUAL reflected quotient:
star on the left free pivot, direct feature on the right. -/
def actualSwapCoefficient (j : SwapIndex EL ER S) : ℂ :=
  H j.1 j.2.1*weight j.1 j.2.1 j.2.2.1*
    if IsCoprime (Ideal.span {j.2.2.2.1.val}) (Ideal.span {j.2.2.2.2.val}) then
      (star (selectedMatrix (EL j.1) S j.2.2.1 j.2.2.2.1)*(A ⟨j.1,j.2.2.2.1⟩*star (FL j.2.2.2.1.val j.2.1)))*
      (selectedMatrix (ER j.2.1) S j.2.2.1 j.2.2.2.2*(B ⟨j.2.1,j.2.2.2.2⟩*FR j.2.2.2.2.val j.1)) else 0

def radialActualSwap (W : 𝓢(ℝ,ℂ)) (R : ℝ) : ℂ :=
  ∑ j : SwapIndex EL ER S, actualSwapCoefficient EL ER S A B FL FR H weight j*
    paperRadialFourier W (R*z j.2.2.1/(x ⟨j.1,j.2.2.2.1⟩*y ⟨j.2.1,j.2.2.2.2⟩))

/-- Exact transposition of the two fibre families. Neither the Schwartz
profile nor its radial Fourier transform is conjugated or replaced. -/
theorem radialActualSwap_eq_transpose (W : 𝓢(ℝ,ℂ)) (R : ℝ) :
    radialActualSwap EL ER S A B FL FR H weight x y z W R =
      radialCoprimeSwap ER EL S B A (fun u v => star (FR u v)) (fun u w => star (FL u w))
        (fun w v => H v w) (fun w v I => weight v w I) y x z W R := by
  unfold radialActualSwap radialCoprimeSwap
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only [actualSwapCoefficient,swapCoefficient]
  simp only [star_star]
  have hcomm : IsCoprime (Ideal.span {q.val}) (Ideal.span {u.val}) ↔
      IsCoprime (Ideal.span {u.val}) (Ideal.span {q.val}) := isCoprime_comm
  rw [hcomm]
  by_cases hc : IsCoprime (Ideal.span {u.val}) (Ideal.span {q.val})
  · simp only [hc,ite_true]
    rw [mul_comm (y ⟨w,q⟩) (x ⟨v,u⟩)]
    ring
  · simp only [hc,ite_false,mul_zero,zero_mul]

end Swap

/-- Uniform common-Mellin bound for the literal radial coprime swap.
The constant precedes ALL finite fibres, vectors, masks, source ranges and
row radii. The only operator bounds are the exact selected squarefree fibre
norms; powers2,3,4 are arbitrary bounded dual multipliers, never norm inputs. -/
theorem common_radial_coprimeSwap_bound (W : 𝓢(ℝ,ℂ)) (decay : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
    ∀ {VL VR : Type} [Fintype VL] [Fintype VR]
      (EL : VL → Finset O) (ER : VR → Finset O) (S : Finset (Ideal O))
      (A : Fibre EL → ℂ) (B : Fibre ER → ℂ) (FL : O → VR → ℂ) (FR : O → VL → ℂ)
      (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
      (x : Fibre EL → ℝ) (y : Fibre ER → ℝ) (z : S → ℝ)
      (KL KR BL BR ε : ℝ) (hε : 0 < ε),
      0 ≤ KL → 0 ≤ KR → 0 ≤ BL → 0 ≤ BR →
      (∀ v, selectedNorm (EL v) S ≤ KL) → (∀ w, selectedNorm (ER w) S ≤ KR) →
      (∀ u w, ‖FL u w‖ ≤ 1) → (∀ u v, ‖FR u v‖ ≤ 1) →
      (∀ v w, ‖H v w‖ ≤ 1) → (∀ v w I, ‖weight v w I‖ ≤ 1) →
      (∀ v, ∀ u : EL v, u.val ≠ 0) → (∀ w, ∀ u : ER w, u.val ≠ 0) →
      (∀ v, ∀ u : EL v, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BL) →
      (∀ w, ∀ u : ER w, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BR) →
      (∀ u, x u ∈ Set.Icc (1 : ℝ) 2) → (∀ u, y u ∈ Set.Icc (1 : ℝ) 2) →
      (∀ I, z I ∈ Set.Icc (1 : ℝ) 2) →
      ‖radialCoprimeSwap EL ER S A B FL FR H weight x y z W R‖ ≤
        (C/(1+R)^decay)*
        (Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2))*
          Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2))) := by
  obtain ⟨C,hC,hsep⟩ := radial_pair_log_separation W decay
  refine ⟨C,hC,?_⟩
  intro R hR VL VR _ _ EL ER S A B FL FR H weight x y z KL KR BL BR ε hε
    hKL hKR hBL hBR hEL hER hFL hFR hH hweight hnL hnR hNL hNR hx hy hz
  obtain ⟨b,hb,hi,hL1,_⟩ := hsep R hR
  let Dcost :=
    Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2))*
      Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2))
  have hD : 0 ≤ Dcost := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpoint (t : ℝ) : ‖coprimeSwap EL ER S (phaseVector A x t) (phaseVector B y t) FL FR H
      (phaseWeight S weight z t)‖ ≤ Dcost := by
    have ht := coprimeSwap_le EL ER S (phaseVector A x t) (phaseVector B y t) FL FR H
      (phaseWeight S weight z t) KL KR BL BR ε hKL hKR hBL hBR hε hEL hER hFL hFR hH
      (phaseWeight_norm_le S weight z hweight t) hnL hnR hNL hNR
    simpa only [phaseVector_norm,Dcost] using ht
  have hp : 0 < (1+R)^decay := by positivity
  have hmass : (∫ t : ℝ, ‖b t‖) ≤ C/(1+R)^decay := by
    apply (le_div_iff₀ hp).2
    nlinarith
  rw [radialCoprimeSwap_eq_integral EL ER S A B FL FR H weight x y z W b R hx hy hz hi hb]
  calc
    _ ≤ ∫ t : ℝ, Dcost*‖b t‖ := by
      apply norm_integral_le_of_norm_le (hi.const_mul Dcost)
      exact Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        have hm := mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg (b t))
        nlinarith only [hm]
    _ = Dcost*(∫ t : ℝ, ‖b t‖) := integral_const_mul _ _
    _ ≤ Dcost*(C/(1+R)^decay) := mul_le_mul_of_nonneg_left hmass hD
    _ = _ := by dsimp [Dcost]; ring

/-- Common-Mellin estimate in the ACTUAL star-left/direct-right quotient
orientation, with unequal independent pivot rays and all masks retained. -/
theorem common_radial_actualSwap_bound (W : 𝓢(ℝ,ℂ)) (decay : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
    ∀ {VL VR : Type} [Fintype VL] [Fintype VR]
      (EL : VL → Finset O) (ER : VR → Finset O) (S : Finset (Ideal O))
      (A : Fibre EL → ℂ) (B : Fibre ER → ℂ) (FL : O → VR → ℂ) (FR : O → VL → ℂ)
      (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
      (x : Fibre EL → ℝ) (y : Fibre ER → ℝ) (z : S → ℝ)
      (KL KR BL BR ε : ℝ) (hε : 0 < ε),
      0 ≤ KL → 0 ≤ KR → 0 ≤ BL → 0 ≤ BR →
      (∀ v, selectedNorm (EL v) S ≤ KL) → (∀ w, selectedNorm (ER w) S ≤ KR) →
      (∀ u w, ‖FL u w‖ ≤ 1) → (∀ u v, ‖FR u v‖ ≤ 1) →
      (∀ v w, ‖H v w‖ ≤ 1) → (∀ v w I, ‖weight v w I‖ ≤ 1) →
      (∀ v, ∀ u : EL v, u.val ≠ 0) → (∀ w, ∀ u : ER w, u.val ≠ 0) →
      (∀ v, ∀ u : EL v, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BL) →
      (∀ w, ∀ u : ER w, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BR) →
      (∀ u, x u ∈ Set.Icc (1 : ℝ) 2) → (∀ u, y u ∈ Set.Icc (1 : ℝ) 2) →
      (∀ I, z I ∈ Set.Icc (1 : ℝ) 2) →
      ‖radialActualSwap EL ER S A B FL FR H weight x y z W R‖ ≤
        (C/(1+R)^decay)*
        (Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2))*
          Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2))) := by
  obtain ⟨C,hC,hbound⟩ := common_radial_coprimeSwap_bound W decay
  refine ⟨C,hC,?_⟩
  intro R hR VL VR _ _ EL ER S A B FL FR H weight x y z KL KR BL BR ε hε
    hKL hKR hBL hBR hEL hER hFL hFR hH hweight hnL hnR hNL hNR hx hy hz
  rw [radialActualSwap_eq_transpose]
  have ht := hbound R hR ER EL S B A (fun u v => star (FR u v)) (fun u w => star (FL u w))
    (fun w v => H v w) (fun w v I => weight v w I) y x z KR KL BR BL ε hε
    hKR hKL hBR hBL hER hEL (by intro u v; simpa only [norm_star] using hFR u v)
    (by intro u w; simpa only [norm_star] using hFL u w)
    (fun w v => hH v w) (fun w v I => hweight v w I) hnR hnL hNR hNL hy hx hz
  have hcost :
      (C/(1+R)^decay)*
        Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2))*
        Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2)) =
      (C/(1+R)^decay)*
        Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2))*
        Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2)) := by ring
  exact ht.trans_eq (by simpa only [mul_assoc] using hcost)

end
end Qrh.JointDetector.FiveColourMellin

#print axioms Qrh.JointDetector.FiveColourMellin.radialCoprimeSwap_eq_integral
#print axioms Qrh.JointDetector.FiveColourMellin.common_radial_coprimeSwap_bound

#print axioms Qrh.JointDetector.FiveColourMellin.common_radial_actualSwap_bound
