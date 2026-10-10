import WeightedQRH.NumeratorReflectionProfiles
import WeightedQRH.NumeratorReflectionMass
import OAI.NumberTheory.DirichletL.Moments.UniformRetainedEnergy

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.WeightedNumeratorReflection
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentRetainedWeightedSource CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentUniformRetainedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_mul_sqrt_fourth (z q : ℂ) :
    ‖z*(Real.sqrt ‖q‖:ℂ)‖^4 = ‖z‖^4*‖q‖^2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  calc
    _ = ((Real.sqrt ‖q‖)^2)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (norm_nonneg _)]

/-- Exact natural primitive restoration, including its summable redundant-prime
and annular packet, transports the rowwise reflected fourth moment. -/
theorem actual_retained_uniform_fourth (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B J : ℕ) (hB : 2 ≤ B) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ ψ : ι → Character) (P : ι → ℂ)
        (X R : ι → ℝ) (lo hi D E Rcap : ℝ),
      (∀i, 0 < X i) → lo ≤ hi →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0 < dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2 ∈ retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) ∈ Set.Icc lo hi) →
      0 < D → 0 ≤ E → (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ) ≤ Rcap) →
      (∀v w : ℝ, ∀j k : Fin 2, ∀x ∈ Set.Icc lo hi, ∀y ∈ Set.Icc lo hi,
        (∑i, ‖polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2) →
      (∑i, ‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)‖^4*‖P i‖^2)
        ≤ C*Rcap^epsilon*D^4*(1+2*(hi-lo))^2*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := reflected_fourth_rowwise_scales B J
  obtain ⟨Cw,hCw,hw⟩ := actual_masked_reflection_fourth epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R lo hi D E Rcap hX hlh hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let keep (i : ι) (u : α i) := u.2 ∈ retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  let c (i : ι) : ℂ := Real.sqrt ‖P i‖
  let f (i : ι) (u : α i) :=
    retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (c i) u
  have hselected (u : ∀i, α i) :
      (∑i, ‖f i (u i)‖^4) ≤ Cp*D^4*(1+2*(hi-lo))^2*E := by
    let Y (i : ι) := if keep i (u i) then
      dyadicScale (u i).2*dualScale (χ i) (ψ i) (X i) (u i).1.1 (u i).1.2
      else Real.exp lo
    let P' (i : ι) := if keep i (u i) then P i else 0
    have hY (i : ι) : 0 < Y i := by
      dsimp [Y]
      split_ifs
      · exact mul_pos (dyadicScale_pos _) (dualScale_pos _ _ _ (hX i) _ _)
      · exact Real.exp_pos _
    have hlogY (i : ι) : Real.log (Y i) ∈ Set.Icc lo hi := by
      dsimp [Y]
      split_ifs with hk
      · exact hgeom i (u i) _ hk
      · simp only [Real.log_exp]; exact ⟨le_rfl,hlh⟩
    have he (v w : ℝ) (j k : Fin 2) (x : ℝ) (hx : x ∈ Set.Icc lo hi)
        (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
        (∑i, ‖polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P' i‖^2)
          ≤ E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
      apply (Finset.sum_le_sum (fun i _ => ?_)).trans (henergy v w j k x hx y hy)
      dsimp only [P']
      split_ifs
      · exact le_rfl
      · simp only [mul_zero,norm_zero,zero_pow (by omega : 2 ≠ 0)]
        exact sq_nonneg _
    have hh := hp G (fun i => (χ i).inverse) P' (fun i => dyadicScale (u i).2)
      Y lo hi D E hlh (fun i => dyadicScale_pos _) hY hlogY hD hE hGD he
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f,retainedColumn]
    simp only [normalized_zero]
    by_cases hk : keep i (u i)
    · simp only [keep] at hk
      rw [if_pos hk]
      dsimp [Y,P',keep,c]
      rw [if_pos hk,if_pos hk,norm_mul_sqrt_fourth]
    · have hk' := hk
      simp only [keep] at hk'
      rw [if_neg hk']
      simp only [norm_zero,zero_pow (by omega : 4 ≠ 0)]
      dsimp [P',keep]
      rw [if_neg hk']
      simp
  have hh := hw (fun i => sourcePrimes (χ i) (ψ i))
    (fun i Q hQ => redundantSet_prime _ _ Q hQ) ψ (fun i => (ψ i).inverse)
    (fun _ => B) (fun _ => hB) Rcap _ hRcap hcap (fun _ _ => 1) f
    (by intro i a; simp) hselected
  simp only [one_mul] at hh
  have hid (i : ι) :
      retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*c i =
      ∑'a, signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) B a*f i a := by
    have he := retainedOriginal_eq_weighted (χ i) (ψ i) (G i) (X i) (R i) 0
      (hX i) B 0 (c i) (hh.1 i)
    simpa only [retained_zero,pow_zero,Complex.ofReal_one,one_mul] using he
  calc
    _ = ∑i, ‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*c i‖^4 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (norm_mul_sqrt_fourth _ (P i)).symm
    _ = ∑i, ‖∑'a, signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) B a*f i a‖^4 := by
      simp_rw [hid]
    _ ≤ Cw*Rcap^epsilon*(Cp*D^4*(1+2*(hi-lo))^2*E) := hh.2
    _ = _ := by ring

end SevenEighths.WeightedNumeratorReflection
end
end OAI
