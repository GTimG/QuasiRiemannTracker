/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.RawSidesSelected
import Candidate.C092.transport.RootColoredSeed
import Candidate.C092.transport.TwistedRawBallSupport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussSelection
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentAddedZeroUniform CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentGaussEnergy CenteredMomentLiveDomain
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumDecEq {κ κ₂ : Type*} : DecidableEq (κ ⊕ κ₂) := Classical.decEq _

def poly (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (u : Id)
    (τ : Character) (t : ℝ) (k : O) : ℂ :=
  gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
    (sourceGenerator_supported (sourceColumns s))
    (fun I => sourceColumn s ha ω₁ ω₂ u I * heightCoeff τ t I) k

theorem poly_tuples (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (u : Id)
    (τ : Character) (t : ℝ) (k : O) :
    poly s ha ω₁ ω₂ u τ t k =
    ∑v∈Fintype.piFinset (MixedPrincipalAllocations.tuplePools s),
      MixedOriginalSecondZero.originalTuple s ha u v * ordinaryColor ω₁ ω₂ v *
        (heightCoeff τ t (finiteTupleProduct v) * primaryGaussRow (finiteTupleProduct v) k) := by
  unfold poly
  rw [MixedFirstLiveSource.source_gauss_sum (sourceColumns s)
    (fun I => sourceColumn s ha ω₁ ω₂ u I * heightCoeff τ t I) k]
  simp_rw [mul_assoc]
  simpa only [mul_assoc] using (source_root_eq_columns s ha ω₁ ω₂ u
    (fun I => heightCoeff τ t I * primaryGaussRow I k)).symm

theorem selected_expansion (s : Source ι a b) (hB1 : ∀k,s.B k=1) (J : Finset ι)
    (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (u : Id) (hu : Squarefree u)
    (τ : Character) (t : ℝ) (k : O) :
    poly s ha ω₁ ω₂ u τ t k =
    ∑y∈selY s J, selScalar s J y τ t *
      ∑I∈sourceColumns (restSource s hB1 J),
        sourceColumn (restSource s hB1 J) ha ω₁ ω₂ (seedRest u (∏j,y j)) I *
          ((if IsCoprime (∏j,y j) I then 1 else 0) * heightCoeff τ t I *
            primaryGaussRow ((∏j,y j)*I) k) := by
  rw [poly_tuples, sum_tuples_split s hB1 J]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← source_root_eq_columns]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hyp : ∀j,Prime (y j) := fun j => s.hp j.val _ (Fintype.mem_piFinset.mp hy j)
  have hvp : ∀i,Prime (v (Sum.inl i)) := fun i =>
    s.hp i.val _ (Fintype.mem_piFinset.mp hv (Sum.inl i))
  have hDn : (∏j,y j) ≠ 0 := (selY_supported s J y hy).1
  have hvn := finiteTupleProduct_ne_zero_of_mem (restSource s hB1 J) v hv
  rw [originalTuple_join s hB1 J ha u y v hyp hvp, finiteTupleProduct_join,
    originalTuple_seed, if_pos (one_dvd _)]
  rw [originalTuple_seed (restSource s hB1 J) ha (seedRest u (∏j,y j)) v]
  rw [dvd_mul_iff_seedRest hu hDn hvn]
  change _ = selScalar s J y τ t * ((if seedRest u (∏j,y j) ∣ finiteTupleProduct v then
    MixedOriginalSecondZero.originalTuple (restSource s hB1 J) ha 1 v else 0) * _ * _)
  rw [CenteredMomentSecondSourceEnergy.heightCoeff_mul]
  unfold selScalar
  change _ * ordinaryColor ω₁ ω₂ v * _ = _
  split_ifs <;> ring

#print axioms selected_expansion
end
end QRH.Cycle092.ColoredGaussSelection
