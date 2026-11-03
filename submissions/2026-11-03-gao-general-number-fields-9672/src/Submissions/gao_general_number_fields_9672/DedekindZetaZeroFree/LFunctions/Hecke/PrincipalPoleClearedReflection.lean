/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/PrincipalPoleClearedReflection.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAndContinuationWitnesses

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {f : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F f}

theorem PrincipalHeckeWitness.U_reflection (p : PrincipalHeckeWitness η) :
    ∀ s : ℂ, p.U s = p.U (1 - s) := by

  have h_agree : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → p.U s = p.U (1 - s) := by
    intro s hs0 hs1
    have hs0' : 1 - s ≠ 0 := by
      rw [sub_ne_zero]
      exact Ne.symm hs1
    have hs1' : 1 - s ≠ 1 := by
      intro h
      exact hs0 (by
        have h2 : (1 : ℂ) + 0 = 1 + s := by simpa using sub_eq_iff_eq_add.mp h
        exact (add_left_cancel h2).symm)
    rw [p.poleClearing s hs0 hs1, p.poleClearing (1 - s) hs0' hs1',
      p.functionalEquation s hs0 hs1]
    ring

  have hfg : p.U =ᶠ[nhds (2 : ℂ)] fun s => p.U (1 - s) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℂ) ≠ 0),
      eventually_ne_nhds (by norm_num : (2 : ℂ) ≠ 1)] with s hs0 hs1
    exact h_agree s hs0 hs1
  have hg : Differentiable ℂ fun s : ℂ => p.U (1 - s) :=
    p.differentiable_U.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have h := AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr p.differentiable_U)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) hfg
  exact fun s => congrFun h s

end DedekindZetaZeroFree.LargeSieve
