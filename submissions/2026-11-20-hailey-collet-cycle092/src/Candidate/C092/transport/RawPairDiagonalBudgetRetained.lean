/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.RawPairDiagonalBudgetUniform
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QRH.Cycle092.RawPairDiagonalBudget
noncomputable section
local instance (priority := 2000) diagSubtypeDecEqRetained {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
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



/-- The native retained first child is priced at its REAL symmetric core;
no stand-alone upper estimate for K is substituted for the two label norms. -/
lemma retained_child_core (s : Source ι a b) (G opp : Id) (hG : Supported G) (hopp : Supported opp)
    (hcpG : commonPart G opp=G) (hcpO : commonPart opp G=opp)
    (E : Finset (CommonIndex G opp)) (τ η : Character)
    (hmod : τ.modulus=η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
      Ideal.span {(72:HeckeFamily.O)}*Ideal.span {primeSubsetGenerator (fun P:CommonIndex G opp=>P.val) E*activeConductor G opp})
    (Kroot Z κ : ℝ) (hZ : 1<Z) (hKroot : Z≤Kroot) (hκ : κ≤1/1500) (n : ℤ)
    (hn : Retained (frequencyRadius (firstNominalScale G opp (∏P∈E,P.val) Kroot (sourceVolume s)) Z κ) n) :
    childScale Z κ n≤4*Z^(1/1000:ℝ)*balancedCore s τ G opp/Z := by
  have hh := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.childScale_le_core G opp hG hopp hcpG hcpO E τ η hmod
    Kroot (sourceVolume s) Z κ κ hZ hKroot (sourceVolume_pos s) n hn
  rw [QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.rpow_freqLoss0 Z κ hZ] at hh
  have hp := Real.rpow_le_rpow_of_exponent_le hZ.le (show 3*κ/2≤(1/1000:ℝ) by linarith)
  exact hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)) (zero_lt_one.trans hZ).le)

lemma selected_width_eventual (N : ℕ) : ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀s : Source ι a b,Fintype.card ι≤N → ∀ (hb : 0≤b) (cover : OriginalEnclosure s)
      (w : ι→ℝ),(∀i,0≤w i) → (∀i,s.P i=Z^(w i)) →
    ∀G : Id,∀Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val),
      (∀B,(∑j∈Js B,w j.val)≤3/5000) →
      ∀B,slotWidth (allocatedLiveSource s hb cover G B) (Js B)≤Z^(1/1000:ℝ) := by
  filter_upwards [RawSides.selected_width_Q N] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hN hb cover w hw hP G Js hJs B
  have hNlive : Fintype.card (liveIndices B.val)≤N := (Fintype.card_subtype_le _).trans hN
  have hp := (hZ.2 (liveIndices B.val) (fun j=>w j.val) hNlive (fun j=>hw j.val) (Js B) (hJs B)).2
  change (∏j:Js B,2*s.P j.val.val)≤Z^(1/1000:ℝ)
  simp_rw [hP]
  exact (Finset.prod_coe_sort (Js B) (fun j=>2*Z^(w j.val))).le.trans hp

/-- Actual source profile/height amplitude, not a new energy hypothesis. -/
lemma profile_cost_le_amplitude (s : Source ι a b) (N : ℕ) (Kslot : ℝ)
    (hN : Fintype.card ι≤N) (hmarks : ∀i,s.M i≤Kslot) (hKs : 1≤Kslot)
    (t₀ V : ℝ) (hV : 0≤V) (J : ℕ) (control : Finset (ℕ×ℕ))
    (h00 : (0,0)∈control) (Cside : ℝ) (hCs : 1≤Cside) :
    profileCap s^2≤4*(Kslot^N)^2*amplitude s t₀ V J control Cside := by
  have hCs0 : 0<Cside := zero_lt_one.trans_le hCs
  have hamp := amplitude_nonneg s t₀ V hV J control Cside hCs0.le
  have hh := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.profileCap_sq_le s control h00 Kslot N hN hmarks hKs
  have hc := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.controls_sq_le_amplitude s t₀ V hV J control Cside hCs0
  exact hh.trans (mul_le_mul_of_nonneg_left (hc.trans (div_le_self hamp hCs)) (by positivity))

/-- Genuine first-child/selected-allocation H.5 price: all coefficients,
heights and opposite-family factors retained, with an arbitrary positive share
fixed before Z. There is no K-core, count, source estimate or energy premise. -/
theorem uniform_retained_diagonal_share (N : ℕ) (Kslot Cz Ct θ : ℝ)
    (hKs : 1≤Kslot) (hCz : 0≤Cz) (hCt : 0≤Ct) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀ (s : Source ι a b),Fintype.card ι≤N → (∀i,s.M i≤Kslot) →
    ∀ (hb : 0≤b) (cover : OriginalEnclosure s) (w : ι→ℝ),
      (∀i,0≤w i) → (∀i,s.P i=Z^(w i)) →
    ∀ (G opp : Id) (hG : Supported G) (hopp : Supported opp),
      commonPart G opp=G → commonPart opp G=opp →
      (G.absNorm:ℝ)≤Z^(8:ℝ) → (opp.absNorm:ℝ)≤Z^(8:ℝ) → (sourceVolume s)⁻¹≤Z^(2:ℝ) →
    ∀ (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val)),
      (∀B,(∑j∈Js B,w j.val)≤3/5000) →
    ∀ (η₁ η₂ τ η : Character) (E : Finset (CommonIndex G opp)),
    τ.modulus=η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
      Ideal.span {(72:HeckeFamily.O)}*Ideal.span {primeSubsetGenerator (fun P:CommonIndex G opp=>P.val) E*activeConductor G opp} →
    ∀ (Kroot κ : ℝ),Z≤Kroot → κ≤1/1500 → ∀n : ℤ,
      Retained (frequencyRadius (firstNominalScale G opp (∏P∈E,P.val) Kroot (sourceVolume s)) Z κ) n →
    ∀ (t t₀ V loss : ℝ),0≤V → 0≤loss → ∀ (J : ℕ) (control : Finset (ℕ×ℕ)),(0,0)∈control →
    ∀Cside : ℝ,1≤Cside →
    secondDiagonalCost s hb cover G Js η₁ η₂ τ t (childScale Z κ n) Z Cz Ct ≤
      θ*balancedBudget s τ G opp (amplitude s t₀ V J control Cside) Z loss := by
  let D : ℝ := 4*(Kslot^N)^2
  have hD : 0<D := by dsimp [D];positivity
  filter_upwards [uniform_second_diagonal_share (ι:=ι) (a:=a) (b:=b) N Kslot Cz Ct (θ/D)
    hKs hCz hCt (div_pos hθ hD),selected_width_eventual (ι:=ι) (a:=a) (b:=b) N] with Z hp hwZ
  refine ⟨hp.1,?_⟩
  intro s hN hmarks hb cover w hw hP G opp hG hopp hcpG hcpO hNG hNO hV Js hJs η₁ η₂ τ η E hmod Kroot κ hKroot hκ n hn t t₀ V loss hVheight hloss J control h00 Cside hCs
  have hW := hwZ.2 s hN hb cover w hw hP G Js hJs
  have hcore := retained_child_core s G opp hG hopp hcpG hcpO E τ η hmod Kroot Z κ hp.1 hKroot hκ n hn
  have hprof := profile_cost_le_amplitude s N Kslot hN hmarks hKs t₀ V hVheight J control h00 Cside hCs
  have hK : 0≤childScale Z κ n := (Real.rpow_nonneg (zero_lt_one.trans hp.1).le _)
  have hh := hp.2 s hN hmarks hb cover G opp hG.1 hopp.1 hNG hNO hV Js hW η₁ η₂ τ t
    (childScale Z κ n) (D*amplitude s t₀ V J control Cside) loss hK hprof hloss hcore
  apply hh.trans_eq
  unfold balancedBudget
  field_simp
  <;> ring
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.uniform_retained_diagonal_share
