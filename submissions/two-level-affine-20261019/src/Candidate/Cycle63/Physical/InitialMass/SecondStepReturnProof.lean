/- The return of the second step at the state left by the fixed deletion of a LOW child, from the generic step and the
producer of the HIGH given. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.SecondStepLedger
import Candidate.Cycle63.Physical.InitialMass.SecondStepFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open Cycle63Moment Cycle63Moment.LowBranch
open CenteredMomentEnergyState CenteredMomentEnergyBands

/-- The second step at the state left by the fixed deletion of a LOW child, from the generic step at the ledger of its
grid position and the count form of its HIGH part. The generic step `hcontract` holds for every schedule `g`. For the
character `η₀`, the ideal `Q` and the ledger of a grid position the producer `hproducer` of the HIGH given chooses the
schedule `g`; then the radial majorant `Ψ` of the generic step and the constants of the producer and of the generic step
follow, and the finitely many ledgers of the grid give the constants of the second step. The state is read in the unit
of its width `W`, between `2/5` and `Mcap`: the mask bound `Bwide` is at least `5/2` the bound `Bpun` of the puncture of
the presented states, the height exponent `τT` of the presentation is divided by `W`, the caps `B` of the records and
the losses `lossNeeded + εc` of the producer are multiplied by `W`, and the exponent `εc` of the old moment is at most
`εold/Mcap`. -/
theorem second_step_return {α : Type} [Fintype α] [DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (εaffine ap bp bΦ Bmask Bwide Bpun Bv L Lslot lo hi Mcap εold εc mesh τT lossFloor B lossNeeded Bnorm : ℝ)
    (G : ℕ) (Presented : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → Prop)
    (hG : 0<G) (hεaffine : 0<εaffine) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp) (hbΦ : 2≤bΦ)
    (hBpun : 0≤Bpun) (hBwide : 5/2*Bpun≤Bwide) (hBwide' : Bwide≤20) (hBv0 : 0≤Bv) (hBv : 5/2*Bv≤B-130)
    (hlo : 33/50≤lo) (hhi : hi≤33/50) (hMcap : 0<Mcap) (hεc : 0<εc) (hεold : Mcap*εc≤εold)
    (hmesh0 : 0 ≤ mesh) (hmeshL : 5/2*Lslot≤ mesh) (hτT : 0<τT/Mcap)
    (hB : 0≤B) (hBnorm : Mcap*B≤Bnorm) (hlossNeeded : 0≤lossNeeded) (hloss : Mcap*(lossNeeded+εc)≤lossFloor)
    (hmeshfloor : ∀ i : Cycle63.SecondIndex G,
      mesh<@Cycle63.AffineLedger.amplifierFloor (Cycle63.secondFamily G i)/2)
    (hres : ∀ i : Cycle63.SecondIndex G,
      128*geometryLossUnit 1 εaffine≤@Cycle63.AffineLedger.lowReserve (Cycle63.secondFamily G i))
    (hmeshdict : mesh≤Cycle25.Energy.commonMesh 2 (28+Bwide) 1 (geometryLossUnit 1 εaffine/8))
    (hmeshproducer : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmeshold : mesh≤Cycle25.Energy.commonMesh 1 Bwide 1 (εc/2))
    (h3δ : 3*geometryFinalDictionaryRate (geometryLossUnit 1 εaffine) 31 3 4 3 130 (3*((Fintype.card α:ℝ)+2))
      (Fintype.card α)≤Cycle63.Optimization.lowReserveWeight)
    (hPres : ∀ (η₀ : Character) (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v₁ : O) (T : ℝ), Presented η₀ Z s v₁ T →
      DepthTwoPresented τT η₀ Z s v₁ T ∧ (s.puncture.absNorm : ℝ)≤Z^Bpun ∧ ((Ideal.span {v₁}).absNorm : ℝ)≤Z^Bv)
    (hcontract : ∀ g : GeometryAffineLowSchedule,
      GeometryAffineAtStateStatement (α:=α) M H hH W hW hWs hβlo hβhi g εaffine ap bp bΦ Bwide mesh εc)
    (hproducer : DepthTwoHighGivenStatement (α:=α) M H hH W hW hWs hβlo hβhi εaffine ap bp bΦ Bwide mesh (τT/Mcap) B
      lossNeeded) :
    SecondStepReturnAt (α:=α) M H hH fourFixedDictionary W 2 ap bp bΦ Bmask L Lslot lo hi Mcap εold Bnorm
      (SecondApplicable G lossFloor Presented) := by
  refine second_step_return_of_body fun η₀ Q hQM hQ0 hQt hQ72 => ?_
  refine second_step_body_of_cover (Part := fun i η₀ Z s v₁ x₁ x₂ z W T len ampB loss =>
      SecondApplicable G lossFloor Presented η₀ Z s v₁ x₁ x₂ z W T len ampB loss ∧
        SecondStepFits G i x₁ x₂ z W len ampB) η₀ Q
    (fun η₀ Z s v₁ x₁ x₂ z W T len ampB loss hz happ => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := secondApplicable_fits hG lossFloor Presented hz happ
    exact ⟨i, happ, hi⟩
  · let _ : Cycle63.AffineLedger := Cycle63.secondFamily G i
    have _ : Cycle63.AffineLedger.DeletesIntoOldRegion := Cycle63.secondFamily_deletesIntoOldRegion G i
    obtain ⟨g, hgμ, hgδ, hgτ, hg⟩ := hproducer hεaffine hap hap' hbp hbΦ (by linarith) hBwide' hmesh0 hmeshproducer hτT
      η₀ Q hQM hQ0 hQt hQ72 _ rfl le_rfl
    obtain ⟨Ψ, hΨsupp, hΨnn, hΨ⟩ := hcontract g hεaffine hgμ (by rw [hgμ]; exact hgδ) hap hap' hbp (by linarith)
      (by linarith) hBwide' hmesh0 hεc
    have hδ : 3*g.δ≤Cycle63.Optimization.lowReserveWeight := by rw [hgδ]; exact h3δ
    obtain ⟨SH, dh, Kcl, hprod⟩ := hg Ψ hΨsupp hΨnn
    obtain ⟨degree, S, -, -, C, Chigh, hC, hChigh, hevAt⟩ :=
      hΨ (hmeshfloor i) (by rw [hgμ]; exact hres i) (by rw [hgμ]; exact hmeshdict) hmeshold η₀ Q hQM hQ0 hQt hQ72 SH dh
    obtain ⟨Kh, hKh, hevGiven⟩ := hprod εc hεc
    refine ⟨Kcl, degree, S, C*(1+Chigh*Kh), by positivity, ?_⟩
    exact second_step_body_of_given M H hH W hW hWs hβlo hβhi g ap bp bΦ Bwide Bmask Bpun Bv L Lslot lo hi Mcap εold εc
      mesh τT lossFloor B lossNeeded Bnorm Kcl Kh C Chigh hap Ψ SH dh degree S η₀ Q hQM hQ72 Presented _ hlo hhi hMcap
      hεc hεold hBpun hBwide hBv0 hBv (by linarith) hgτ hB hBnorm hlossNeeded hloss hC hChigh hKh hPres
      (fun η₀ Z s v₁ x₁ x₂ z W T len ampB loss h => secondFamily_part i lossFloor g.δ hδ Presented h.1 h.2) hevAt
      hevGiven

end
end OAI.SevenEighths.Cycle63InitialMass
