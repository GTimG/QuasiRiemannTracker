/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fix the common stage mesh before any finite ray data. Price the actual
dictionary uniformly from the full regular source on strictly earlier bands. -/
import Candidate.C092.transport.ActualEarlierP2Bank
import Candidate.C092.transport.ActualStageFrameBudgetPhysicalBank
import Candidate.C092.transport.ActualStageFrameBudgetSelect
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open QRH.SilDensitySplit.CubeFree.FP
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.RegularFramePhysicalReturn QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.FixedRayPair QRH.Cycle090 QRH.SourceCertificate
namespace QRH.Cycle092.ActualStageFrameBudget
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- Chooses one finite genuine bank before any source query at U. Its
threshold may depend on the finite fixed characters, but not on columns,
inverse divisors, either live ordinary length or any height. -/
def EarlyPhysicalBanks (n y mesh δ:ℝ) (hδ:0<δ) : Prop :=
  ∀ (N:ℕ) (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ) (hHr:RayOrthogonality.globalUnits M ≤ Hr)
    (W:ℝ→ℂ) (hW:ContDiff ℝ ∞ W) (hWs:Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (bΦ:ℝ) (hbΦ:2 ≤ bΦ) (hΦ:Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η base ω₁ ω₂:Character) (Q:Id) (hQM:Q ≤ M) (hQ₀:Q≠0) (hQt:Q≠⊤)
    (h72:Q ≤ Ideal.span {(72:O)}) (hb:Q ≤ base.modulus)
    (hω₁:Q ≤ ω₁.modulus) (hω₂:Q ≤ ω₂.modulus),
    let θ:=fun k:Fin (N+1)=>frameData N k.val M Hr hHr W hW hWs base Q hQM hQ₀ hQt h72 hb
    let Kslot:=RestoredRootSource.slotBound W hW.continuous hWs
    ∃bank:NativePhysicalBank N,bank.Fee ∧ ∀ᶠ Z:ℝ in atTop,bank.At θ η ω₁ ω₂ Q mesh δ n y Kslot Z hδ

theorem actual_stage_banks {n y l ε:ℝ} (hε:0<ε) (hβ:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (earlier:EarlierCover PairOpenWidth y) (hy₀:sourceY0 ≤ y) (hy₁:y ≤ sourceY)
    (hyn:y ≤ n) (hn:n ≤ sourceRatio*y) (hl:l<sourceWidth n y) :
    let loss:=ε/8
    ∃δ mesh:ℝ,0<δ ∧ 0 < mesh ∧ δ ≤ loss/250 ∧ δ ≤ (rho:ℝ)/10000 ∧
      mesh ≤ δ ∧ l+mesh ≤ sourceWidth n y ∧ mesh ≤ 1/100 ∧ mesh ≤ 1/6 ∧
      (3*(10*δ)<loss) ∧ (∀hδ:0<δ,EarlyPhysicalBanks n y mesh δ hδ) := by
  dsimp only
  obtain ⟨δ,m,hδ,hm,hδloss,hδrho,hmd,hlm,hm1,hm6,_,_⟩:=early_parameters hl (by linarith:0<ε/8)
  obtain ⟨mP,hP,p2⟩:=actual_earlier_p2_bank hβ earlier hy₀ hy₁ hyn hn
  obtain ⟨mF,hF,hframe⟩:=actual_physical_bank δ hδ
  let mesh:=min m (min mP mF)
  have hmm:mesh ≤ m:=min_le_left _ _
  have hmp:mesh ≤ mP:=(min_le_right _ _).trans (min_le_left _ _)
  have hmf:mesh ≤ mF:=(min_le_right _ _).trans (min_le_right _ _)
  have hmpos:0 < mesh:=lt_min hm (lt_min hP hF)
  refine ⟨δ,mesh,hδ,hmpos,hδloss,hδrho,hmm.trans hmd,by linarith,hmm.trans hm1,hmm.trans hm6,by linarith,?_⟩
  intro hδ' N M inst Hr hHr W hW hWs bΦ hbΦ hΦ η base ω₁ ω₂ Q hQM hQ₀ hQt h72 hb hω₁ hω₂
  have h0:internalQ Q base=Q:=inf_eq_left.mpr hb
  have h1:internalQ Q (base.product ω₁)=Q:=(internalQ_product Q base ω₁ hω₁).trans h0
  have h2:internalQ Q (base.product ω₂)=Q:=(internalQ_product Q base ω₂ hω₂).trans h0
  obtain ⟨D,S,C,hC,hbank⟩:=p2 mesh hmp N M Hr hHr W hW hWs bΦ hbΦ hΦ η base ω₁ ω₂ Q hQM
    (by simpa only [h1] using hQ₀) (by simpa only [h1] using hQt) (by simpa only [h1] using h72) (by simpa only [h2] using hQ₀) (by simpa only [h2] using hQt) (by simpa only [h2] using h72)
  exact hframe mesh hmpos hmf N M Hr hHr W hW hWs base Q hQM hQ₀ hQt h72 hb
    bΦ hbΦ hΦ hβ n y hy₀ hy₁ hyn η ω₁ ω₂ hω₁ hω₂ D S C hC hbank _
    (RestoredRootSource.slotBound_spec W hW.continuous hWs).1

#print axioms actual_stage_banks
end QRH.Cycle092.ActualStageFrameBudget
