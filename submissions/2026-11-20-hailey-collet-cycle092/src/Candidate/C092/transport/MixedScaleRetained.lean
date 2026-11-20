/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Reflect one genuine physical numerator while the complete witness, reciprocal
or marked product is kept as an arbitrary independent row multiplier. -/
import Candidate.C092.transport.MixedScaleUnit
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CenteredMomentRetainedWeightedSource CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentUniformRetainedEnergy
open CenteredMomentNaturalPrimitive CenteredMomentScaleSupremum
namespace QRH.Cycle092.MixedScale

theorem retained_independent_multiplier (ε : ℝ) (hε : 0<ε) (B J : ℕ) (hB : 2≤B) :
    ∃ H : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧ ∀ {ι : Type} [Fintype ι],
      ∀ (G : ι→𝓢(ℝ,ℂ)) (χ ψ : ι→Character) (P : ι→ℂ) (X R : ι→ℝ) (lo hi D E Rcap : ℝ),
      (∀ i,0<X i) → lo≤hi →
      (∀ i (j : Index (sourcePrimes (χ i) (ψ i))),
        ∀ hY : 0<dualScale (χ i) (ψ i) (X i) j.1.1 j.1.2,
        j.2 ∈ retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) j.1.1 j.1.2) hY →
        Real.log (dyadicScale j.2*dualScale (χ i) (ψ i) (X i) j.1.1 j.1.2)∈Set.Icc lo hi) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      1≤Rcap → (∀i,(Ideal.absNorm (∏ q∈sourcePrimes (χ i) (ψ i),q):ℝ)≤Rcap) →
      (∀ v : ℝ, ∀ j : Fin 2, ∀ x∈Set.Icc lo hi,
        (∑ i, ‖polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*P i‖^2) ≤ E*(1+‖v‖)^(2*J)) →
      (∑ i,‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*P i‖^2)
        ≤ C*Rcap^ε*D^2*(1+2*(hi-lo))*E := by
  obtain ⟨H,C,hC,hsrc⟩ := actual_retained_uniform_energy ε hε B J hB
  let A := 1+∑ k : Fin 2,‖scaleTest unitWindow k 1‖^2
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨H,C*A,mul_pos hC hA,?_⟩
  intro ι _ G χ ψ P X R lo hi D E Rcap hX hlh hgeom hD hE hG hRcap hcap hmoment
  have ht := hsrc G χ ψ P X R (fun _ => 0) (fun _ => 0) unitWindow (1/2) (3/2) lo hi 0 0 D (A*E) Rcap
    hX (by norm_num) unitWindow_support unitWindow_smooth hlh le_rfl (fun _ => ⟨le_rfl,le_rfl⟩)
    hgeom hD (mul_nonneg hA.le hE) hG hRcap hcap (by
      intro v j k x hx y hy
      have hzero := le_antisymm hy.2 hy.1
      subst y
      simp only [Real.exp_zero,one_ideal_only _ _ (scaleTest_support _ _ _ unitWindow_support k)]
      let f := fun i => polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)
      let b := scaleTest unitWindow k 1
      have hb : ‖b‖^2 ≤ A := by
        have := Finset.single_le_sum (f:=fun k : Fin 2 => ‖scaleTest unitWindow k 1‖^2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ k)
        dsimp only [b,A]; linarith
      change ∑ i,‖f i*b*P i‖^2 ≤ _
      calc
        _ = ‖b‖^2*∑ i,‖f i*P i‖^2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
          simp only [norm_mul,mul_pow]; ring
        _ ≤ A*(E*(1+‖v‖)^(2*J)) := mul_le_mul hb (hmoment v j x hx) (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hA.le
        _ = _ := by ring)
  simp only [Real.exp_zero,unitWindow_polynomial,one_mul,sub_self,mul_zero,add_zero,mul_one] at ht
  exact ht.trans_eq (by ring)

#print axioms retained_independent_multiplier
end QRH.Cycle092.MixedScale
end
