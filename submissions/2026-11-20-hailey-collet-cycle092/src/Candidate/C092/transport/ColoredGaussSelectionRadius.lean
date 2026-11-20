/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.ColoredGaussSelectionActual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussSelection
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def scale (s : Source ι a b) (J : Finset ι) : ℝ := ∏j:↥J,2*s.P j.val

theorem scale_one_le (s : Source ι a b) (J : Finset ι) : 1 ≤ scale s J := by
  apply Finset.one_le_prod₀
  intro j _
  have := s.hP j.val
  linarith

theorem selected_norm_le_scale (s : Source ι a b) (J : Finset ι) (y : ↥J→Id)
    (hy : y∈selY s J) : ((∏j,y j).absNorm:ℝ) ≤ scale s J := by
  simp only [map_prod, Nat.cast_prod]
  apply Finset.prod_le_prod₀
  · intro j _; positivity
  · intro j _
    exact (s.hpn j.val _ (Fintype.mem_piFinset.mp hy j)).2

theorem selected_radius (s : Source ι a b) (J : Finset ι) (K : ℝ) (hK : 0<K)
    (y : ↥J→Id) (hy : y∈selY s J) :
    2*K*‖ConcreteTraceCRT.eisEmbedding (CompletedGauss.primaryGenerator (∏j,y j)^4)‖^2 ≤
      16*K*(scale s J)^4 := by
  have hD := selY_supported s J y hy
  have hn := CompletedGauss.primaryGenerator_norm_sq (∏j,y j)
    (supported_primaryGenerator_ne_zero _ hD)
  have hb := selected_norm_le_scale s J y hy
  have hpow := pow_le_pow_left₀ (show (0:ℝ)≤((∏j,y j).absNorm:ℝ) by positivity) hb 4
  rw [map_pow, norm_pow, ← pow_mul, show 4*2=2*4 by decide, pow_mul, hn]
  calc
    2*K*((∏j,y j).absNorm:ℝ)^4 ≤ 2*K*(scale s J)^4 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 16*K*(scale s J)^4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith

open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock

theorem scale_eq_actual {ι : Type} [Fintype ι] (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    scale (allocatedLiveSource s hb cover G B) J = RawSides.selectionScaleQ s hb cover G B J := by
  unfold scale RawSides.selectionScaleQ
  exact Finset.prod_coe_sort J (fun j => 2*(allocatedLiveSource s hb cover G B).P j)

/-- Actual first raw side, including all frozen ordinary colors and its original
    normalization, reaches exactly the radii and Vsets of original_second_zero_tail_Q. -/
theorem raw_sum_le_selected_radius {ι : Type} [Fintype ι] (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Id→*₀ℂ) (C D G opposite : Id)
    (hD : D≠0) (hOpp : Supported opposite) (hG : Supported G)
    (hOppG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (J : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (τ : Character) (t K : ℝ) (hK : 0<K) :
    (∑u∈concreteArtificial s C D hD,
      TwistedRawBall.rawEnergy s ha ω₁ ω₂ opposite G hG u τ t K) / sourceVolume s ≤
    ((actualAllocations (tuplePools s) G).card *
      ∑B : actualAllocations (tuplePools s) G,TwistedRawBall.allocationWeight s ω₁ ω₂ G B *
        selectedTerms (allocatedLiveSource s hb cover G B) (fun _=>rfl) (J B) ha ω₁ ω₂
          (concreteArtificial s C D hD) τ t
          (fun _=>16*K*(RawSides.selectionScaleQ s hb cover G B (J B))^4)) / sourceVolume s := by
  apply raw_sum_le_selected s ha hb cover ω₁ ω₂ opposite G hOpp hG hOppG
    (concreteArtificial s C D hD) (concreteArtificial_squarefree s C D hD) J τ t K _ hK
  · intro B y hy
    have hs := scale_one_le (allocatedLiveSource s hb cover G B) (J B)
    rw [scale_eq_actual] at hs
    positivity
  · intro B y hy
    rw [← scale_eq_actual]
    exact selected_radius (allocatedLiveSource s hb cover G B) (J B) K hK y hy

#print axioms selected_radius
#print axioms raw_sum_le_selected_radius
end
end QRH.Cycle092.ColoredGaussSelection
