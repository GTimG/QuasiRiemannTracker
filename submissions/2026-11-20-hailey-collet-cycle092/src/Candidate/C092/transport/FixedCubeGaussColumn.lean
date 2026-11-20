/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.FixedCubeApplication
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteLabelAssembly12

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedHeightEnergy MixedCommonCoefficient MixedCommonAllocation MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def ordinaryPool₁ (s : Source ι a b) : Finset Id :=
  residualPool s.d.1 s.hd.1 (plainSupportPool b s.X₁ s.Y₁)

def ordinaryPool₂ (s : Source ι a b) : Finset Id :=
  residualPool s.d.2 s.hd.2 (plainSupportPool b s.X₂ s.Y₂)

/-- The actual frozen assignment scalar; the original injectivity test stays
inside the signed sum and no distinct assignment is discarded silently. -/
def markScalar (s : Source ι a b) (p : (i : ι) → s.pool i) (w : Id →*₀ ℂ) : ℂ :=
  if Function.Injective (fun i => (p i).val) then
    (∏ i,s.ν i (p i)*s.Wslot i ((Ideal.absNorm (p i).val : ℝ)/s.P i))*w (∏ i,(p i).val) else 0

/-- The literal remaining two-ordinary coefficient after freezing actual marks.
It retains both original prefixes, puncture, full seed-divisor indicator,
cubefreeness and supplying-prime deletion from Sil's C.7 restriction. -/
def frozenOrdinaryTerm (s : Source ι a b) (ha : 0 < a) (seed M : Id)
    (w : Id →*₀ ℂ) (I J : Id) : ℂ :=
  if Candidate.FourthPower.SexticSieve.PowerFree 3 (I*J) ∧
      IsCoprime (punctureProduct s.S s.H*M) (I*J) ∧
      IsCoprime (M*I*J) s.R ∧ seed ∣ M*I*J then
    w I*w J*idealRectangle
      (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.d.1*I) (s.d.2*J) else 0

def frozenOrdinaryRow (s : Source ι a b) (ha : 0 < a) (seed M : Id) (w : Id →*₀ ℂ) : ℂ :=
  ∑ I : ordinaryPool₁ s,∑ J : ordinaryPool₂ s,frozenOrdinaryTerm s ha seed M w I J

/-- Exact native finite-column/mark-assignment identity before any norms or
H8 estimate. This preserves the source's signed reference rectangle and all
original seed, puncture, supplying and profile-prefix data. -/
theorem sourceCoefficient_frozen_marks (s : Source ι a b) (ha : 0 < a) (seed : Id) (w : Id →*₀ ℂ) :
    (∑ K ∈ sourceColumns s,sourceCoefficient s ha seed K*w K)=
      ∑ p : (i : ι) → s.pool i,markScalar s p w*frozenOrdinaryRow s ha seed (∏ i,(p i).val) w := by
  unfold sourceColumns sourceCoefficient originalColumn MixedPrincipalAllocations.tuplePools
  rw [finite_column_regroup]
  have hpools : MixedLiteralAllocation.sourcePools s.pool s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂=
      CenteredMomentSourceRectangle.tuplePools s.pool (ordinaryPool₁ s) (ordinaryPool₂ s) := by
    funext j
    cases j with
    | inl i => rfl
    | inr j => fin_cases j <;> rfl
  rw [hpools]
  have hdec : (MixedPrincipalWindow.instDecidableEqSumFinOfNatNat_submissions : DecidableEq (ι ⊕ Fin 2)) =
      (inferInstance : DecidableEq (ι ⊕ Fin 2)) := Subsingleton.elim _ _
  rw [hdec]
  have hsplit (f : Tuple ι → ℂ) :
      (∑ v ∈ Fintype.piFinset (CenteredMomentSourceRectangle.tuplePools s.pool (ordinaryPool₁ s) (ordinaryPool₂ s)),f v)=
        ∑ p : (i : ι) → s.pool i,∑ I : ordinaryPool₁ s,∑ J : ordinaryPool₂ s,
          f (CenteredMomentSourceRectangle.pack (fun i => (p i).val) I J) := by
    simpa only [CenteredMomentSourceRectangle.tuplePool] using
      CenteredMomentSourceRectangle.sum_tuplePool s.pool (ordinaryPool₁ s) (ordinaryPool₂ s) f
  refine (hsplit _).trans ?_
  apply Finset.sum_congr rfl
  intro p _
  unfold frozenOrdinaryRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  simp only [tupleWeight,tupleRestriction,restriction,slotProduct,profileCoefficient,
    pack_slot,pack_left,pack_right,pack_product,map_mul]
  by_cases hinj : Function.Injective (fun i => (p i).val)
  · simp only [markScalar,hinj,ite_true]
    unfold frozenOrdinaryTerm
    split_ifs <;> simp_all only [and_self, and_true, and_false, true_and, false_and,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, mul_zero, zero_mul] <;> ring
  · simp only [hinj,and_false,ite_false,zero_mul,markScalar]

#print axioms sourceCoefficient_frozen_marks
end
end QRH.Cycle092.FixedCubeGauss
