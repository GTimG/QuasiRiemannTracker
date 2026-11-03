/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Fourier/AdelicFiniteLevelTorus.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.UniformSmoothLevelFamilies
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SmoothCompactTorusExpansion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaAdditiveFourier.FiniteLevelDescent
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]
  (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))

def descend (f : SmoothAdeleQuotient F → ℂ) : finiteLevelAdditiveQuotient K → ℂ :=
  fun t => f (Quotient.out t)

theorem descend_mk (f : SmoothAdeleQuotient F → ℂ)
    (hf : HasSmoothAdditiveLevel K f) (q : SmoothAdeleQuotient F) :
    descend K f (QuotientAddGroup.mk q) = f q := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add (finiteLevelImage K) q
  unfold descend
  rw [hr]
  exact hf q r

theorem continuous_descend_family {P : Type*} [TopologicalSpace P]
    (f : P × SmoothAdeleQuotient F → ℂ)
    (hf : ∀ p, HasSmoothAdditiveLevel K (fun q => f (p, q)))
    (hc : Continuous f) :
    Continuous (fun z : P × finiteLevelAdditiveQuotient K =>
      descend K (fun q => f (z.1, q)) z.2) := by
  apply ((IsOpenQuotientMap.id (X := P)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := finiteLevelImage K))).continuous_comp_iff.mp
  convert hc using 1
  funext z
  exact descend_mk K (fun q => f (z.1, q)) (hf z.1) z.2

def torusFamily {d P : Type*} [TopologicalSpace P]
    (e : finiteLevelAdditiveQuotient K ≃ₜ+ UnitAddTorus d)
    (f : P × SmoothAdeleQuotient F → ℂ) : P → UnitAddTorus d → ℂ :=
  fun p t => descend K (fun q => f (p, q)) (e.symm t)

theorem torusFamily_mk {d P : Type*} [TopologicalSpace P]
    (e : finiteLevelAdditiveQuotient K ≃ₜ+ UnitAddTorus d)
    (f : P × SmoothAdeleQuotient F → ℂ)
    (hf : ∀ p, HasSmoothAdditiveLevel K (fun q => f (p, q)))
    (p : P) (q : SmoothAdeleQuotient F) :
    torusFamily K e f p (e (QuotientAddGroup.mk q)) = f (p, q) := by
  simp only [torusFamily, e.symm_apply_apply]
  exact descend_mk K _ (hf p) q

theorem continuous_torusFamily {d P : Type*} [TopologicalSpace P]
    (e : finiteLevelAdditiveQuotient K ≃ₜ+ UnitAddTorus d)
    (f : P × SmoothAdeleQuotient F → ℂ)
    (hf : ∀ p, HasSmoothAdditiveLevel K (fun q => f (p, q)))
    (hc : Continuous f) :
    Continuous (fun z : P × UnitAddTorus d => torusFamily K e f z.1 z.2) := by
  exact (continuous_descend_family K f hf hc).comp
    (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))

section Haar
variable {d : Type*} [Fintype d]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def coordinateMap (e : finiteLevelAdditiveQuotient K ≃ₜ+ UnitAddTorus d) :
    SmoothAdeleQuotient F →+ UnitAddTorus d :=
  e.toAddEquiv.toAddMonoidHom.comp (QuotientAddGroup.mk' (finiteLevelImage K))

end Haar

end DedekindZetaZeroFree.ThetaAdditiveFourier.FiniteLevelDescent

end
