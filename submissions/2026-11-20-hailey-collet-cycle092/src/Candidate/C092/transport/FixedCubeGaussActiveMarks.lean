/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussFrozenFactors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussActiveMarks_250ee732072daf03_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- The combined common/full-primary frozen marked ideal has the original
annulus cap. Only the frozen profile values are used, so true zero terms
need no artificial pool or conductor hypotheses. -/
lemma combined_frozen_mark_cap (r : Source ι a b) (B : Tuple ι) (E : Tuple (liveIndices B))
    (G F R₁ R₂ : Id) (ν : ι→Id→ℂ) (μ : liveIndices B→Id→ℂ)
    (hB : frozenCoefficient B G R₁ ν r.Wslot r.P≠0)
    (hE : frozenCoefficient E F R₂ μ (fun i:liveIndices B=>r.Wslot i.val)
      (fun i:liveIndices B=>r.P i.val)≠0)
    (i : ι) (hfrozen : B (Sum.inl i)*liftPrimaryTuple B E (Sum.inl i)≠1) :
    (Ideal.absNorm (B (Sum.inl i)*liftPrimaryTuple B E (Sum.inl i)):ℝ)≤2*r.P i := by
  by_cases hi : B (Sum.inl i)=1
  · have hmem : i∈liveIndices B := by simp only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,hi]
    let j : liveIndices B:=⟨i,hmem⟩
    have hval : liftPrimaryTuple B E (Sum.inl i)=E (Sum.inl j) := by
      simp [liftPrimaryTuple,hmem,j]
    rw [hi,one_mul,hval] at hfrozen ⊢
    exact frozenCoefficient_mark_cap E F R₂ μ (fun j:liveIndices B=>r.Wslot j.val)
      (fun j:liveIndices B=>r.P j.val) 2
      (fun j x hx=>(r.hW j.val hx).2) (fun j=>zero_lt_one.trans_le (r.hP j.val)) hE j hfrozen
  · have hn : i∉liveIndices B := by simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hval : liftPrimaryTuple B E (Sum.inl i)=1 := by simp [liftPrimaryTuple,hn]
    rw [hval,mul_one]
    exact frozenCoefficient_mark_cap B G R₁ ν r.Wslot r.P 2
      (fun j x hx=>(r.hW j hx).2) (fun j=>zero_lt_one.trans_le (r.hP j)) hB i hi

/-- Native marked norm cap on an active frozen scalar, with no relation
between arithmetic mask values at distinct ordinary coordinates. -/
lemma actual_frozen_mark_cap (r : Source ι a b) (B : Tuple ι) (G R : Id) (ν : ι→Id→ℂ)
    (hB : frozenCoefficient B G R ν r.Wslot r.P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    (Ideal.absNorm (B (Sum.inl i)):ℝ)≤2*r.P i :=
  frozenCoefficient_mark_cap B G R ν r.Wslot r.P 2
    (fun j x hx=>(r.hW j hx).2) (fun j=>zero_lt_one.trans_le (r.hP j)) hB i hi

lemma shiftedSlotCoefficient_norm_le_one (r : Source ι a b) (v : ℝ) (i : ι) (I : Id) (hI : I≠0) :
    ‖shiftedSlotCoefficient r v i I‖≤1 := by
  unfold shiftedSlotCoefficient
  rw [CenteredMomentCommonMaskEnergy.heightCoefficient_norm (r.ν i) v I hI]
  exact r.hν i I

/-- Literal squared scalar payment, retaining each frozen marked profile
bound and inverse scale. This is before replacing scales by frozen norms. -/
lemma normalized_frozen_squared_bound (r : Source ι a b) (B : Tuple ι) (G R : Id)
    (ν : ι→Id→ℂ) (hν : ∀i,‖ν i (B (Sum.inl i))‖≤1) :
    ‖(MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B=>r.P i.val))⁻¹)*
      frozenCoefficient B G R ν r.Wslot r.P‖^2≤
    ∏i : ι with B (Sum.inl i)≠1,(r.M i)^2/(r.P i) := by
  rw [norm_mul,mul_pow,normalization_ratio_norm_sq]
  have hc := frozenCoefficient_norm_le B G R ν r.Wslot r.P r.M
    (fun i=>zero_le_one.trans (r.hM i)) hν r.hWnorm
  calc
    _ ≤ (∏i:ι with B (Sum.inl i)≠1,(r.P i)⁻¹)*(∏i:ι with B (Sum.inl i)≠1,r.M i)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc 2)
        (Finset.prod_nonneg (fun i _=>inv_nonneg.mpr (zero_le_one.trans (r.hP i))))
    _ = _ := by
      rw [←Finset.prod_pow,←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring

lemma shifted_normalized_frozen_squared_bound (r : Source ι a b) (B : Tuple ι) (G R : Id)
    (hB : ∀j,B j≠0) (v : ℝ) :
    ‖(MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B=>r.P i.val))⁻¹)*
      frozenCoefficient B G R (shiftedSlotCoefficient r v) r.Wslot r.P‖^2≤
    ∏i : ι with B (Sum.inl i)≠1,(r.M i)^2/(r.P i) :=
  normalized_frozen_squared_bound r B G R (shiftedSlotCoefficient r v)
    (fun i=>shiftedSlotCoefficient_norm_le_one r v i _ (hB _))

#print axioms shiftedSlotCoefficient_norm_le_one
#print axioms normalized_frozen_squared_bound
#print axioms shifted_normalized_frozen_squared_bound
#print axioms combined_frozen_mark_cap
#print axioms actual_frozen_mark_cap
end
end QRH.Cycle092.FixedCubeGauss
