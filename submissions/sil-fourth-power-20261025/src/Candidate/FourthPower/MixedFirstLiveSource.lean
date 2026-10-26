/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first residual sources after genuine common extraction. The
artificial divisor becomes the ORIGINAL seed of the live source; it is
not erased. Ordinary prefixes, heights and tuple restrictions are exact.
-/
import Candidate.FourthPower.MixedOriginalSecondZero
import Candidate.FourthPower.MixedSupplierReconstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstLiveSource
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentLattice CenteredMomentSourceRectangle CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedCommonEnergy MixedLiveRows
open MixedHeightEnergy MixedOriginalSecondZero MixedSupplierReconstruction MixedRestrictedDictionary
open MixedLiteralAllocation CenteredMomentLiveDomain
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The exact remaining source. Its genuine extraction has already
been done, hence the new frozen tuple and common ideal are both one.
The former full common ideal stays in R and both ordinary prefixes. -/
def liveSource (s : Source ι a b) : Source (liveIndices s.B) a b where
  S := s.S
  H := s.H
  pool := fun i=>s.pool i.val
  d := s.prefixPair
  hd := s.prefixPair_nonzero
  B := fun _=>1
  hB := fun _=>one_ne_zero
  G := 1
  R := s.R*s.G
  Fhole := s.Fhole
  hprod := by simp only [finiteTupleProduct,Finset.prod_const_one]
  hR := mul_ne_zero s.hR s.common_nonzero
  hFhole := s.hFhole
  ν := fun i=>s.ν i.val
  Wslot := fun i=>s.Wslot i.val
  P := fun i=>s.P i.val
  M := fun i=>s.M i.val
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁
  t₂ := s.t₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  U₁ := s.U₁
  U₂ := s.U₂
  T := s.T
  L := s.L
  hL := s.hL
  hX₁ := s.hX₁
  hX₂ := s.hX₂
  hY₁ := s.hY₁
  hY₂ := s.hY₂
  hXU₁ := s.hXU₁
  hXU₂ := s.hXU₂
  hYU₁ := s.hYU₁
  hYU₂ := s.hYU₂
  hpX := s.hpX
  hpY := s.hpY
  hP := fun i=>s.hP i.val
  hM := fun i=>s.hM i.val
  hpool := fun i=>s.hpool i.val
  hp := fun i=>s.hp i.val
  hpn := fun i=>s.hpn i.val
  hν := fun i=>s.hν i.val
  hWnorm := fun i=>s.hWnorm i.val
  hW := fun i=>s.hW i.val
  hS := s.hS
  hH := s.hH
  henclose := by
    intro I hI hi
    apply s.henclose I hI
    simpa only [Source.prefixPair,mul_one] using hi

theorem live_source_box (s : Source ι a b) :
    Fintype.piFinset (tuplePools (liveSource s))=liveBox (tuplePools s) s.B s.hB := by
  exact (source_live_box s.pool s.d s.hd (plainSupportPool b s.X₁ s.Y₁)
    (plainSupportPool b s.X₂ s.Y₂) s.B s.hB).symm

theorem live_source_columns (s : Source ι a b) :
    sourceColumns (liveSource s)=finiteColumns (liveBox (tuplePools s) s.B s.hB) := by
  unfold sourceColumns
  rw [live_source_box]

/-- A seed restriction depends only on the whole column product. This
is an exact finite identity, including zero and nonsquarefree seeds. -/
theorem column_seed_mask {α : Type*} [Fintype α]
    (Q : Finset (Tuple α)) (H R D I : Id) (ν : α→Id→ℂ)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) :
    finiteColumnCoefficient Q
      (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 D v) I=
      if D∣I then finiteColumnCoefficient Q
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ d.1 d.2 1 v) I else 0 := by
  by_cases hD : D∣I
  · rw [if_pos hD]
    unfold finiteColumnCoefficient
    apply Finset.sum_congr rfl
    intro v hv
    have hdv : D∣finiteTupleProduct v := (Finset.mem_filter.mp hv).2.symm ▸ hD
    exact (profile_seed_mask H R D ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d v).symm.trans
      (if_pos hdv)
  · rw [if_neg hD]
    unfold finiteColumnCoefficient
    apply Finset.sum_eq_zero
    intro v hv
    have hdv : ¬D∣finiteTupleProduct v := by simpa only [(Finset.mem_filter.mp hv).2] using hD
    exact (profile_seed_mask H R D ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d v).symm.trans
      (if_neg hdv)

/-- The exact artificial-divisor masked live coefficient, with the
same two independent ordinary heights as the original source. -/
theorem live_source_coefficient (s : Source ι a b) (ha : 0<a) (D I : Id) :
    sourceCoefficient (liveSource s) ha D I=
      if D∣I then finiteColumnCoefficient (liveBox (tuplePools s) s.B s.hB)
        (fun v=>tupleWeight (punctureProduct s.S s.H) v*
          liveProfile s.B s.G s.R s.ν s.Wslot s.P
            (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
            (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
            s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 v) I else 0 := by
  change finiteColumnCoefficient (Fintype.piFinset (tuplePools (liveSource s)))
    (fun v=>tupleWeight (punctureProduct s.S s.H) v*
      profileCoefficient (s.R*s.G) (fun i=>s.ν i.val) (fun i=>s.Wslot i.val) (fun i=>s.P i.val)
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        s.X₁ s.X₂ s.Y₁ s.Y₂ s.prefixPair.1 s.prefixPair.2 D v) I=_
  rw [live_source_box,column_seed_mask]
  rfl

def allocatedLiveSource (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) :=
  liveSource (allocationSource s hb cover G B)

/-- Expand a canonical source before specializing to dependent live
indices. This avoids higher-order rewriting through allocation proofs. -/
theorem source_gauss_tuples (s : Source ι a b) (ha : 0<a) (D : Id)
    (τ : Character) (t : ℝ) (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s))
      (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha D I*heightCoeff τ t I) k=
      ∑v∈Fintype.piFinset (tuplePools s),originalTuple s ha D v*
        (heightCoeff τ t (finiteTupleProduct v)*primaryGaussRow (finiteTupleProduct v) k) := by
  calc
    _ = ∑I∈sourceColumns s,(sourceCoefficient s ha D I*heightCoeff τ t I)*primaryGaussRow I k :=
      source_gauss_sum (sourceColumns s) (fun I=>sourceCoefficient s ha D I*heightCoeff τ t I) k
    _ = ∑I∈sourceColumns s,sourceCoefficient s ha D I*(heightCoeff τ t I*primaryGaussRow I k) := by
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ = _ := finite_column_sum (Fintype.piFinset (tuplePools s)) (originalTuple s ha D)
      (fun I=>heightCoeff τ t I*primaryGaussRow I k)

/-- Exact first Gauss row, now a finite sum of canonical live original
sources. The only coefficient changes are the proved common extraction
and the exact new seed. This works on BOTH sides: C and G need only
have the same prime support, exactly as in the actual first block. -/
theorem first_gauss_live_sources (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (C G seed D : Id)
    (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C=
      QRH.Record1252270103KernelMass.primeSupport G) (hseed : seed∣G)
    (τ : Character) (t : ℝ) (k : O) :
    gaussPolynomial Finset.univ
      (CenteredMomentFirstPhysicalSource.element C G hG.1 (sourceColumns s))
      (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 (sourceColumns s))
      (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 (sourceColumns s)=>
        originalResidual s ha seed G D I*heightCoeff τ t I) k=
      ∑B : actualAllocations (tuplePools s) G,
        (frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*
        gaussPolynomial Finset.univ
          (sourceGenerator (sourceColumns (allocatedLiveSource s hb cover G B)))
          (sourceGenerator_supported (sourceColumns (allocatedLiveSource s hb cover G B)))
          (fun I : supportedColumns (sourceColumns (allocatedLiveSource s hb cover G B))=>
            sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I*heightCoeff τ t I) k := by
  have he := first_gauss_common_tuples (punctureProduct s.S s.H) (tuplePools s)
    (source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂)
    (fun i I hI=>s.hp i I hI) C G s.R seed D hC hG hCG hseed s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d τ t k
  change _=∑B : actualAllocations (tuplePools s) G,_ at he
  apply he.trans
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun x : ℂ=>(frozenWeight (punctureProduct s.S s.H) B.val*
    frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*x)
  refine Eq.trans ?_ (source_gauss_tuples (allocatedLiveSource s hb cover G B) ha D τ t k).symm
  apply Finset.sum_congr (live_source_box (allocationSource s hb cover G B)).symm
  intro v hv
  have hm := profile_seed_mask (punctureProduct s.S s.H) (s.R*G) D
    (fun i : liveIndices B.val=>s.ν i.val) (fun i=>s.Wslot i.val) (fun i=>s.P i.val)
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) v
  exact congrArg (fun x : ℂ=>x*(heightCoeff τ t (finiteTupleProduct v)*
    primaryGaussRow (finiteTupleProduct v) k)) hm

end
end Candidate.FourthPower.MixedFirstLiveSource
