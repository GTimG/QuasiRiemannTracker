/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColumn
import Candidate.C092.transport.RawSidesGrouped
import Submissions.sil_density_split_20261026.CubeFree.Second.Provider

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSupport
open CenteredMomentSecondMovingSupport CenteredMomentFirstSectors
open CenteredMomentFirstSectorTransform CenteredMomentSourceRow CenteredMomentActiveSource
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedFirstCommonSum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- H.5's diagonal collapse follows from the native actual Gauss support,
not from replacing the two common labels by a diagonal by definition. -/
theorem cubeFree_commonCorrelation_diagonal (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (hcf : Packet.CubeFreeCommon C D)
    (w : O) (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w) ≠ 0) : C=D := by
  have hexp : ∀ P : CommonIndex C D,leftExponent C D P=rightExponent C D P := by
    intro P
    by_contra hn
    have hdvd := actual_unequal_min_six C D hC hD hCD w hne P hn
    rcases hcf P with ⟨hl,hr⟩
    rcases hl with hl | hl <;> rcases hr with hr | hr <;> simp_all
  calc
    C = ∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P :=
      (left_ideal_product C D hC hCD).symm
    _ = ∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P :=
      Finset.prod_congr rfl (fun P _=>by rw [hexp P])
    _ = D := right_ideal_product C D hC hD hCD

/-- The native source's complete common labels meet the local 1-or-2 contract. -/
theorem source_commonCorrelation_diagonal (r : Source ι a b) (ha : 0<a)
    (p : Labels r ha 1) (w : O)
    (hne : idealCorrelation p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).2
      (commonFrequencyGenerator p.val.1 p.val.2*w) ≠0) : p.val.1=p.val.2 := by
  have hd := commonLabels_data _ _ p.val.1 p.val.2 p.property
  exact cubeFree_commonCorrelation_diagonal _ _ _ _ hd.2.2
    (Second.Provider.first_label_cubeFree r ha p) w hne

/-- Every off-diagonal common Gauss coefficient in the actual completed
source vanishes, before absolute values and independently of the row frequency. -/
theorem source_offDiagonal_commonCorrelation_zero (r : Source ι a b) (ha : 0<a)
    (p : Labels r ha 1) (hneq : p.val.1≠p.val.2) (w : O) :
    idealCorrelation p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).2
      (commonFrequencyGenerator p.val.1 p.val.2*w)=0 := by
  by_contra hn
  exact hneq (source_commonCorrelation_diagonal r ha p w hn)

#print axioms cubeFree_commonCorrelation_diagonal
#print axioms source_commonCorrelation_diagonal
#print axioms source_offDiagonal_commonCorrelation_zero
end
end QRH.Cycle092.FixedCubeGauss
