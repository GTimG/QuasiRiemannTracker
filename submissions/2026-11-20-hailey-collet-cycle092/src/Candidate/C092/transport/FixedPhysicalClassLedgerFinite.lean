/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Fixed one-sided source energy and its genuine packed twin on native labels.
The keep is the actual inducing classifier, never the regular complement. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerPolynomial
import Candidate.C092.transport.FixedPhysicalClassLedgerAssembly
import Candidate.C092.transport.ColoredGaussFrameProviderActual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open CenteredMomentSecondMaskedWindow CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentSecondSectorColumns CenteredMomentRowNorm
open QRH.Cycle092.FixedFourierH15 QRH.Cycle092.SignedCenter
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource
open QRH.SilDensitySplit.CubeFree
open CenteredMomentRestrictedSourceNormalization CenteredExceptionalProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.TwistedRawSource QRH.Cycle092.RegularColoredForward
namespace QRH.Cycle092.FixedPhysicalClassLedger
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

/-- Every summand of the literal fixed frame energy, before its one native
packed-row injection. -/
def rowEnergy (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (x : GLabel θ mesh Z) (v : ℝ) (z : O) : ℝ :=
  if hf:Fits η rs x then if initialFixed (x.char rs) Q z then
    ‖rowPolynomial Finset.univ (sourceGenerator (residualPool x.G hf.G_ne (sourceColumns s)))
      (fun I : supportedColumns (residualPool x.G hf.G_ne (sourceColumns s))=>
        (if IsCoprime x.G (I:Id) ∧ x.D∣(I:Id) then
          sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) x.seed (x.G*I) else 0)*heightCoeff (x.char rs) v I) z‖^2*
      (ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re else 0 else 0

lemma rowEnergy_pos (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (x : GLabel θ mesh Z) (hf : Fits η rs x) (v : ℝ) (z : O) :
    0 ≤ rowEnergy s ha ω₁ ω₂ η rs Q x v z := by
  unfold rowEnergy
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
  · rfl

lemma rowEnergy_summable (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (x : GLabel θ mesh Z) (hf : Fits η rs x) (v : ℝ) :
    Summable (rowEnergy s ha ω₁ ω₂ η rs Q x v) := by
  change Summable (fun z=>rowEnergy s ha ω₁ ω₂ η rs Q x v z)
  simp only [rowEnergy,dif_pos hf]
  exact restricted_summable (initialFixed (x.char rs) Q) Finset.univ
    (sourceGenerator (residualPool x.G hf.G_ne (sourceColumns s)))
    (sourceGenerator_supported _) _ ballProfile _ (dyadicScale_pos _)

lemma gEnergy_eq_rows (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (x : GLabel θ mesh Z) (hf : Fits η rs x) (v : ℝ) :
    gEnergy s ha ω₁ ω₂ η rs Q x v=FixedFramePacking.prefixNorm x*rs.norm*
      ∑'z : O,rowEnergy s ha ω₁ ω₂ η rs Q x v z := by
  unfold gEnergy rawEnergy
  rw [dif_pos hf]
  simp only [rowEnergy,dif_pos hf]
  rfl

/-- Arbitrary finite native H15/H17 sums give the complete original fixed
frame energy. No truncation, missing row, or extra row-count factor is used. -/
theorem finite_budget_to_frame (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (labels : Finset (GLabel θ mesh Z))
    (fit : ∀x∈labels,Fits η rs x) (v B : ℝ)
    (hfinite : ∀F : Finset O,∑x∈labels,gWeight x*(FixedFramePacking.prefixNorm x*rs.norm*
      ∑z∈F,rowEnergy s ha ω₁ ω₂ η rs Q x v z) ≤ B) :
    ∑x∈labels,gWeight x*gEnergy s ha ω₁ ω₂ η rs Q x v ≤ B := by
  let f := fun x z=>gWeight x*(FixedFramePacking.prefixNorm x*rs.norm*rowEnergy s ha ω₁ ω₂ η rs Q x v z)
  have hn : 0 ≤ rs.norm := by
    unfold GSrc.norm
    exact div_nonneg (Real.rpow_nonneg (zero_lt_one.trans rs.hZ).le _) (sq_nonneg _)
  let Fz := fun z=>∑x∈labels,f x z
  have hFnn : ∀z,0 ≤ Fz z := by
    intro z
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (gWeight_nonneg x) (mul_nonneg
      (mul_nonneg (by unfold FixedFramePacking.prefixNorm;positivity) hn)
      (rowEnergy_pos s ha ω₁ ω₂ η rs Q x (fit x hx) v z))
  have hFfin : ∀F : Finset O,∑z∈F,Fz z ≤ B := by
    intro F
    rw [show (∑z∈F,Fz z)=∑x∈labels,gWeight x*(FixedFramePacking.prefixNorm x*rs.norm*
        ∑z∈F,rowEnergy s ha ω₁ ω₂ η rs Q x v z) from by
      unfold Fz
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [f,Finset.mul_sum]]
    exact hfinite F
  have ht := Real.tsum_le_of_sum_le hFnn hFfin
  have hs : ∀x∈labels,Summable (f x) := by
    intro x hx
    exact ((rowEnergy_summable s ha ω₁ ω₂ η rs Q x (fit x hx) v).mul_left _).mul_left _
  rw [show (∑'z,Fz z)=∑x∈labels,∑'z,f x z from Summable.tsum_finsetSum hs] at ht
  apply le_trans (le_of_eq ?_) ht
  apply Finset.sum_congr rfl
  intro x hx
  simp only [f,gEnergy_eq_rows s ha ω₁ ω₂ η rs Q x (fit x hx) v,tsum_mul_left]

#print axioms finite_budget_to_frame
end QRH.Cycle092.FixedPhysicalClassLedger
