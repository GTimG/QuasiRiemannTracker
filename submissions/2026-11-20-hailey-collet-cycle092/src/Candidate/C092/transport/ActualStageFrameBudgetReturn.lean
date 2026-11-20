/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Install the genuine finite physical bank before both Poisson fees and use
the actual stage horizon to close the source induction at the canonical Q. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierStage
import Candidate.C092.transport.ActualStageFrameBudgetStage
import Candidate.C092.transport.FinalCycle092FromAverage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open QRH.SilDensitySplit.CubeFree.FP RepairedSourceSideSupply
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.RegularFramePhysicalReturn
open QRH.Cycle092.LowActual QRH.Cycle092.StrongPair QRH.Cycle092.FixedRayPair
open QRH.Cycle090 QRH.SourceCertificate
namespace QRH.Cycle092.ActualStageFrameBudget
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- The family consumer has a genuine numerical bank and its single event
already in hand. The normalized source has the original two independent
pitches and the true restored slot data. -/
def OriginalFamilyReturn (n y l mesh ε δ:ℝ) (hm:mesh ≤ 1/6) (hd:0<δ) : Prop :=
  ∀(Slot:Type)[Fintype Slot][DecidableEq Slot](M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr)(W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)
    (hWs:Function.support W ⊆ Set.Icc (1:ℝ) 2)(bΦ:ℝ)(hbΦ:2 ≤ bΦ)
    (hΦ:Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂:Character)(Q₁ Q₂:Id),
    let base:=η₀₁.product η₁.inverse
    let q:=stageQ Q₁ η₀₁ base η₁ η₂
    ∀(hQM:q ≤ M)(hQ₀:q≠0)(hQt:q≠⊤)(h72:q ≤ Ideal.span {(72:O)})
      (hqbase:q ≤ base.modulus),
    let N:=Fintype.card Slot
    let θ:=fun k:Fin (N+1)=>frameData N k.val M Hr hHr W hW hWs base q hQM hQ₀ hQt h72 hqbase
    let K:=RestoredRootSource.slotBound W hW.continuous hWs
    ∀ bank:NativePhysicalBank N,bank.Fee →
      (∀ᶠ Z:ℝ in atTop,bank.At θ ColoredRootRestore.bareBase η₁ η₂ q mesh δ n y K Z hd) →
    ∀ (Cz Ct:RootShape Slot→ℝ),(∀k,0<Cz k ∧ 0<Ct k) →
    ∀ᶠ Z:ℝ in atTop,∀hZ:1<Z,CenteredFramesAt M Hr hHr n y l W hW.continuous hWs bΦ mesh ε Z hZ hm
      η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ bank.degree bank.controls bank.J 1 δ δ (ε/8) (mesh/4) Cz Ct q bank.totalFee (10*δ)

theorem frames_from_family {n y l mesh ε δ:ℝ} (hm:mesh ≤ 1/6) (hd:0<δ)
    (prepared:EarlyPhysicalBanks n y mesh δ hd) (realize:OriginalFamilyReturn n y l mesh ε δ hm hd) :
    NativeFramesStageSupply n y l mesh ε 1 δ δ (ε/8) (mesh/4) (10*δ) hm := by
  intro Slot fin dec M inst Hr hHr W hW hWs bΦ hbΦ hΦ η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hq1 hn1 ht1 h721 hq2 hn2 ht2 h722
  dsimp only
  intro hQ₀ hQt hQM h72 hbase hω₁ hω₂ hqbase hq₁ hq₂
  let base:=η₀₁.product η₁.inverse
  let q:=stageQ Q₁ η₀₁ base η₁ η₂
  obtain ⟨bank,fee,event⟩:=prepared (Fintype.card Slot) M Hr hHr W hW hWs bΦ hbΦ hΦ
    ColoredRootRestore.bareBase base η₁ η₂ q hQM hQ₀ hQt h72 hbase hω₁ hω₂
  refine ⟨bank.J,bank.degree,bank.controls,bank.mem_controls,?_⟩
  intro Cz Ct hcost
  exact ⟨bank.totalFee,add_nonneg bank.fixed_pos.le bank.regular_pos.le,
    realize Slot M Hr hHr W hW hWs bΦ hbΦ hΦ η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQM hQ₀ hQt h72 hbase bank fee event Cz Ct hcost⟩

/-- Final epsilon schedule. The input prices physical families of an
already constructed bank. No candidate bound is declared here. -/
theorem record_of_family_return (family:
    ∀ n y l ε δ mesh:ℝ,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
    0 ≤ l → l < sourceWidth n y → 0<ε → (hδ:0<δ) → (hm:0 < mesh) →
    δ ≤ (ε/8)/250 → δ ≤ (rho:ℝ)/10000 → mesh ≤ δ → l+mesh ≤ sourceWidth n y →
    mesh ≤ 1/100 → (hmesh:mesh ≤ 1/6) → OriginalFamilyReturn n y l mesh ε δ hmesh hδ) :
    HeckeZeroSupremum.beta ≤ Cycle090.theta ∧
    (∀ (η:Character) (s:ℂ),Cycle090.theta<s.re → (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧ Cycle090.OrdinaryTarget := by
  apply Final.target_of_averaged_stages
  intro hβ hcontrary n y hy0 hy1 hyn hn cover l hl0 hl ε hε
  obtain ⟨δ,mesh,hδ,hm,hδloss,hρ,hmd,hlm,hm1,hm6,hgap,hbank⟩:=
    actual_stage_banks hε hβ cover hy0 hy1 hyn hn hl
  have hκ:δ ≤ 1/1500:=by norm_num [rho] at hρ;linarith
  have hf:=family n y l ε δ mesh hy0 hy1 hyn hn hl0 hl hε hδ hm hδloss hρ hmd hlm hm1 hm6
  have hsource:=frames_from_family hm6 hδ (hbank hδ) hf
  refine ⟨mesh,1,δ,δ,mesh/4,ε/8,ε/8,hm,hm6,le_rfl,hδ,hδ,by linarith,by linarith,by linarith,by linarith,?_⟩
  exact native_averaged_of_frames n y l mesh ε 1 δ (ε/8) (mesh/4) (10*δ)
    hy0 hy1 hn hl.le hlm hm.le hm6 le_rfl hκ (by positivity) hgap (by linarith) hsource

#print axioms frames_from_family
#print axioms record_of_family_return
end QRH.Cycle092.ActualStageFrameBudget
