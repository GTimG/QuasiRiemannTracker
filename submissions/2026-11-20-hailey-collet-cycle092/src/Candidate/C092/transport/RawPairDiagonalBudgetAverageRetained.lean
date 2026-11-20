/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.RawPairDiagonalBudgetAverageUniform
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QRH.Cycle092.RawPairDiagonalBudget
noncomputable section
local instance (priority := 2000) diagSubtypeDecEqAverageRetained {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst ActualEisensteinCubic
open RepairedSourceSideSupply
open CenteredMomentSectorLocalization
open MixedFirstExceptionalWindow
open MixedFirstLiveSource MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type} [Fintype ι] {a b : ℝ}



theorem uniform_retained_average_diagonal_share (N : ℕ) (Kslot Cz Ct θ : ℝ)
    (hKs : 1≤Kslot) (hCz : 0≤Cz) (hCt : 0≤Ct) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀ (s : Source ι (1/4) (9/4)),Fintype.card ι≤N → (∀i,s.M i≤Kslot) →
    ∀ (cover : OriginalEnclosure s) (w : ι→ℝ),
      (∀i,0≤w i) → (∀i,s.P i=Z^(w i)) →
    ∀ (G opp : Id) (hG : Supported G) (hopp : Supported opp),
      commonPart G opp=G → commonPart opp G=opp →
      (G.absNorm:ℝ)≤Z^(8:ℝ) → (opp.absNorm:ℝ)≤Z^(8:ℝ) → (sourceVolume s)⁻¹≤Z^(2:ℝ) →
    ∀ (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val)),
      ∀ M : actualAllocations (tuplePools s) G→ℝ,
    (∀B,0 ≤ M B) →
    (∀B,M B ≤ (selY (allocatedLiveSource s (by norm_num) cover G B) (Js B)).card) →
    (∀B,(∑j∈Js B,w j.val)≤3/5000) →
    ∀ (η₁ η₂ τ η : Character) (E : Finset (CommonIndex G opp)),
    τ.modulus=η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
      Ideal.span {(72:HeckeFamily.O)}*Ideal.span {primeSubsetGenerator (fun P:CommonIndex G opp=>P.val) E*activeConductor G opp} →
    ∀ (Kroot κ : ℝ),Z≤Kroot → κ≤1/1500 → ∀n : ℤ,
      Retained (frequencyRadius (firstNominalScale G opp (∏P∈E,P.val) Kroot (sourceVolume s)) Z κ) n →
    ∀ (t t₀ V loss : ℝ),0≤V → 0≤loss → ∀ (J : ℕ) (control : Finset (ℕ×ℕ)),(0,0)∈control →
    ∀Cside : ℝ,1≤Cside →
    secondAverageDiagonalCost s cover G Js η₁ η₂ τ t (childScale Z κ n) Z Cz Ct M ≤
      θ*balancedBudget s τ G opp (amplitude s t₀ V J control Cside) Z loss := by
  let D : ℝ := 4*(Kslot^N)^2
  have hD : 0<D := by dsimp [D];positivity
  filter_upwards [uniform_second_average_diagonal_share (ι:=ι) N Kslot Cz Ct (θ/D)
    hKs hCz hCt (div_pos hθ hD),selected_width_eventual (ι:=ι) (a:=1/4) (b:=9/4) N] with Z hp hwZ
  refine ⟨hp.1,?_⟩
  intro s hN hmarks cover w hw hP G opp hG hopp hcpG hcpO hNG hNO hV Js M hM0 hM hJs η₁ η₂ τ η E hmod Kroot κ hKroot hκ n hn t t₀ V loss hVheight hloss J control h00 Cside hCs
  have hW := hwZ.2 s hN (by norm_num) cover w hw hP G Js hJs
  have hcore := retained_child_core s G opp hG hopp hcpG hcpO E τ η hmod Kroot Z κ hp.1 hKroot hκ n hn
  have hprof := profile_cost_le_amplitude s N Kslot hN hmarks hKs t₀ V hVheight J control h00 Cside hCs
  have hK : 0≤childScale Z κ n := (Real.rpow_nonneg (zero_lt_one.trans hp.1).le _)
  have hh := hp.2 s hN hmarks cover G opp hG.1 hopp.1 hNG hNO hV Js M hM0 hM hW η₁ η₂ τ t
    (childScale Z κ n) (D*amplitude s t₀ V J control Cside) loss hK hprof hloss hcore
  apply hh.trans_eq
  unfold balancedBudget
  field_simp
  <;> ring
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.uniform_retained_average_diagonal_share
