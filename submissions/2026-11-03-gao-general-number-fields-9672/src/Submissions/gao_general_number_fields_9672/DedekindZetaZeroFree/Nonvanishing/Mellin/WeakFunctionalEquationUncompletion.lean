/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/WeakFunctionalEquationUncompletion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem weakFE_uncompletion (P : WeakFEPair ℂ) (hk : P.k = 1)
    (q u : ℂ → ℂ) (hq : Differentiable ℂ q) (hu : Differentiable ℂ u)
    (hqu : ∀ s : ℂ, q s = s * u s) :
    let f : ℂ → ℂ := fun s =>
      q s * P.Λ₀ s - u s * P.f₀ - q s * (P.ε / (1 - s)) * P.g₀
    DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → f s = q s * P.Λ s := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => P.ε / (1 - s)) ({1}ᶜ : Set ℂ) := by
    refine DifferentiableOn.div ?_ ?_ ?_
    · exact differentiableOn_const P.ε
    · exact (differentiableOn_const 1).sub differentiableOn_id
    · intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      exact fun h => hx (sub_eq_zero.mp h).symm
  have h1 : DifferentiableOn ℂ (fun s => q s * P.Λ₀ s) ({1}ᶜ : Set ℂ) :=
    (hq.differentiableOn.mono (Set.subset_univ _)).mul
      (P.differentiable_Λ₀.differentiableOn.mono (Set.subset_univ _))
  have h2 : DifferentiableOn ℂ (fun s => u s * P.f₀) ({1}ᶜ : Set ℂ) :=
    (hu.differentiableOn.mono (Set.subset_univ _)).mul_const _
  have h3 : DifferentiableOn ℂ (fun s => q s * (P.ε / (1 - s)) * P.g₀) ({1}ᶜ : Set ℂ) :=
    ((hq.differentiableOn.mono (Set.subset_univ _)).mul hd).mul_const _
  constructor
  · exact (h1.sub h2).sub h3
  · intro s hs0 hs1
    dsimp only
    rw [WeakFEPair.Λ, hk]
    simp only [smul_eq_mul]
    push_cast
    have hqs : q s * (1 / s) = u s := by rw [hqu s]; field_simp
    rw [mul_sub, mul_sub]
    have e2 : q s * (1 / s * P.f₀) = u s * P.f₀ := by rw [← mul_assoc, hqs]
    have e3 : q s * (P.ε / (1 - s) * P.g₀) = q s * (P.ε / (1 - s)) * P.g₀ := by
      rw [mul_assoc]
    rw [e2, e3]

end DedekindZetaZeroFree.AbelianQuotient
