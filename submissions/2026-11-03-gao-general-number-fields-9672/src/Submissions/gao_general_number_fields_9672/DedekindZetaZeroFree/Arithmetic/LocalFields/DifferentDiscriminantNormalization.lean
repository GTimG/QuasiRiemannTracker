/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/DifferentDiscriminantNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.FundamentalDomainScaling

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.BallMeasureBalance

theorem prod_sqrt_absNorm_pow_differentExponent (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (hS : PoissonS.ContainsDifferent F S) :
    ∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ PoissonS.differentExponent F v.val).sqrt =
      Real.sqrt |(NumberField.discr F : ℝ)| := by
  have hD : differentIdeal ℤ (RingOfIntegers F) ≠ 0 := differentIdeal_ne_bot
  have hd : ∀ v, v ∉ S → differentExponent F v = 0 := by
    intro v hv
    rw [differentExponent, FractionalIdeal.count_coe F v hD]
    norm_cast
    by_contra hc
    exact hv (hS v ((Associates.count_ne_zero_iff_dvd hD v.irreducible).mp hc))
  have hfactor : (∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^
      differentExponent F v.val) =
      (FractionalIdeal.coeIdeal (differentIdeal ℤ (RingOfIntegers F)) :
        FractionalIdeal (RingOfIntegers F)⁰ F) := by
    rw [show (∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal :
      FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v.val) =
      ∏ v ∈ S, (FractionalIdeal.coeIdeal v.asIdeal :
      FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v from
      Finset.prod_coe_sort S (fun v => (FractionalIdeal.coeIdeal v.asIdeal :
        FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v)]
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hD)]
    symm
    apply finprod_eq_finsetProd_of_mulSupport_subset
    intro v hv
    by_contra h
    exact hv (by change (_ : FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v = 1; rw [hd v h, zpow_zero])
  have hnorm := congrArg (fun I : FractionalIdeal (RingOfIntegers F)⁰ F =>
    (FractionalIdeal.absNorm I : ℝ)) hfactor
  simp only [map_prod, map_zpow₀, FractionalIdeal.coeIdeal_absNorm,
    Rat.cast_prod, Rat.cast_zpow, Rat.cast_natCast] at hnorm
  rw [NumberField.absNorm_differentIdeal F, Nat.cast_natAbs, Int.cast_abs] at hnorm
  rw [← Real.sqrt_prod (s := Finset.univ)]
  · exact congrArg Real.sqrt hnorm
  · intro v hv
    exact le_of_lt (zpow_pos (by exact_mod_cast
      (lt_trans Nat.zero_lt_one (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.val))) _)

end DedekindZetaZeroFree.PoissonS.BallMeasureBalance

end
