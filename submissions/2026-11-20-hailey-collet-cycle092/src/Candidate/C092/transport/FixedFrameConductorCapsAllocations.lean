/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedFrameConductorCapsCore
import Candidate.C092.transport.FixedPhysicalPaymentAll
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFrameConductorCaps
local notation "Id" => Ideal HeckeFamily.O
variable {L mesh Z : ℝ} {θ : GData L}
local instance c092LocalInst_Candidate_C092_transport_FixedFrameConductorCapsAllocations_67e97984f218adcb_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- A single harmless polynomial exponent is fixed before Z. -/
def budgetExponent (θ : GData L) : ℝ := (θ.N:ℝ)+3*θ.Bmask+128

lemma budgetExponent_large (θ : GData L) : 27 ≤ budgetExponent θ := by
  unfold budgetExponent
  have := θ.hBmask
  have := Nat.cast_nonneg (α:=ℝ) θ.N
  linarith

lemma canonical_mark_cap (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z)
    (hP : ∀i,s.P i=Z^(rs.w i)) (hmesh : mesh≤1) : ∀i,s.P i≤Z := by
  intro i
  rw [hP i]
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le rs.hZ.le ((rs.hwm i).trans hmesh))

/-- The remaining ordinary mark slots inject once into the original slots.
The full allocation/deletion multiplicities stay in the H15 coefficient. -/
lemma surviving_mark_product (s : Source (Fin θ.N) θ.a θ.b) (G D : Id)
    (B : commonAlloc s G) (E : fullPrimaryAlloc s G B D)
    (hZ : 1<Z) (hP : ∀i,s.P i≤Z) :
    (∏i:liveIndices E.val,2*s.P i.val.val) ≤ (2:ℝ)^θ.N*Z^(θ.N:ℝ) := by
  classical
  have hs : (∏i:liveIndices E.val,2*s.P i.val.val) ≤ ∏i:Fin θ.N,2*s.P i := by
    apply Finset.prod_le_prod_of_injOn₀ (fun i:liveIndices E.val=>i.val.val)
    · intro i hi j hj h
      exact Subtype.ext (Subtype.ext h)
    · exact Finset.subset_univ _
    · intro i hi; exact le_rfl
    · intro i hi; exact mul_nonneg (by norm_num) (zero_le_one.trans (s.hP _))
    · intro i hi hn
      linarith [s.hP i]
  apply hs.trans
  calc
    _ ≤ ∏i:Fin θ.N,2*Z := Finset.prod_le_prod₀
      (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
      (fun i _=>mul_le_mul_of_nonneg_left (hP i) (by norm_num))
    _ = (2:ℝ)^θ.N*Z^(θ.N:ℝ) := by simp [mul_pow,Real.rpow_natCast]

/-- The native completion's actual supplier budget is polynomial uniformly
in every B/E allocation, with the original hole ideal and original marks. -/
theorem allocation_budget (θ : GData L) (hZ : 1<Z) (hconst : (2:ℝ)^θ.N≤Z) :
    ∀ {mesh : ℝ} (s : Source (Fin θ.N) θ.a θ.b)
      (rs : GSrc θ mesh Z) (η : Character) (x : GLabel θ mesh Z), Fits η rs x →
      s.Fhole=1 → (s.R.absNorm:ℝ)≤Z^(8:ℝ) → (∀i,s.P i≤Z) →
      (x.G.absNorm:ℝ)≤Z^(budgetExponent θ) ∧ (x.D.absNorm:ℝ)≤Z^(budgetExponent θ) ∧
      ∀ (B : commonAlloc s x.G) (E : fullPrimaryAlloc s x.G B x.D),
        (s.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*s.P i.val.val)*s.R.absNorm*
          x.G.absNorm*x.D.absNorm ≤ Z^(budgetExponent θ) := by
  intro mesh s rs η x hf hhole hR hP
  have hm : θ.Bmask≤budgetExponent θ := by
    unfold budgetExponent
    have := θ.hBmask
    have := Nat.cast_nonneg (α:=ℝ) θ.N
    linarith
  have hmG : 2*θ.Bmask≤budgetExponent θ := by
    unfold budgetExponent
    have := θ.hBmask
    have := Nat.cast_nonneg (α:=ℝ) θ.N
    linarith
  refine ⟨hf.G_cap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hmG),
    hf.D_cap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hm),?_⟩
  intro B E
  have hG := hf.G_cap
  have hD := hf.D_cap
  have hs := surviving_mark_product s x.G x.D B E hZ hP
  rw [hhole,map_one,Nat.cast_one,one_mul]
  calc
    _ ≤ ((2:ℝ)^θ.N*Z^(θ.N:ℝ))*Z^(8:ℝ)*Z^(2*θ.Bmask)*Z^θ.Bmask := by
      gcongr
    _ ≤ (Z*Z^(θ.N:ℝ))*Z^(8:ℝ)*Z^(2*θ.Bmask)*Z^θ.Bmask := by
      gcongr
    _ = Z^((θ.N:ℝ)+3*θ.Bmask+9) := by
      rw [show ((θ.N:ℝ)+3*θ.Bmask+9)=((1+(θ.N:ℝ))+8)+(2*θ.Bmask)+θ.Bmask by ring]
      rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_add (zero_lt_one.trans hZ),
        Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by unfold budgetExponent; linarith)

/-- Actual allocation/deletion, prefix absorption and the native reindex
preserve Fhole literally. In particular no empty-H inference is needed. -/
lemma originalSelectedSource_Fhole {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    (ColoredGaussFrameProvider.originalSelectedSource s hb cover G B J).Fhole=s.Fhole := rfl

#print axioms budgetExponent_large
#print axioms canonical_mark_cap
#print axioms surviving_mark_product
#print axioms allocation_budget
#print axioms originalSelectedSource_Fhole
end QRH.Cycle092.FixedFrameConductorCaps
