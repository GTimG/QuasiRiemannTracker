/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original native fixed Fourier rows, with every scalar debit, reach H.17.
The actual admissible group and source/weight identifications remain explicit. -/
import Candidate.C092.transport.FixedFourierH15NativeRows
import Candidate.C092.transport.FixedFrameTerminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSmooth
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentDivisorAllocation
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentFirstAmplificationChoice ConcreteTraceCRT CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonHeights
open QRH.Cycle092.SignedCenter
open MixedPrincipalWindow MixedCommonRestriction CenteredMomentFiniteProfileExceptional
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFramePacking
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedFourierH15NativeFilled_b8e35bbdbed1bac6_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- A literal native Fourier row at the packed quadratic frequency. -/
def fixedWindowRow (s : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (D : Id)
    (t θ X : ℝ) (V : ℝ→ℂ) (z : O) : ℂ :=
  rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
    (fun I=>divisorCoefficient D (sectorElement G hG.1 (sourceColumns s))
      (CenteredMomentSecondScaled.movingCoefficient 1 (sectorElement G hG.1 (sourceColumns s))
        (fun I=>TwistedRawSource.sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)*heightCoeff η t I)) χ I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) z

/-- Uniform H.15 is applied to data constructed from the actual fixed-row
classifier. There is no numerical row-energy or character-factorization input.
The literal row energy includes its ball profile and both original colors.
The original scalar Fourier/profile costs and source/prefix ledger are explicit. -/
theorem native_fixed_window_filled {frameL : ℝ} (Θ : GData frameL)
    (ha : 0<Θ.a) (hb : 0 ≤ Θ.b) (ω₁ ω₂ : Character)
    (ε Bcap : ℝ) (hε : 0<ε) (hBcap : 0 ≤ Bcap) :
    ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),∃ hS : (0,0)∈S,
    ∀ Q : Id,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀ (mesh : ℝ) (gr : GSrc Θ mesh U) (η : Character)
      (hQ₀ : Q ≠ 0) (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
      (m : O) (hm : m ≠ 0) (hlam : ConcretePrimeRowBridge.goodLambda ∣ m) (ht : (2:O) ∣ m)
      (labels : Finset (GLabel Θ mesh U)) (rows : GLabel Θ mesh U→Finset O)
      (src : GLabel Θ mesh U→Source (Fin Θ.N) Θ.a Θ.b)
      (rowWeight : GLabel Θ mesh U→ℝ)
      (hG : ∀x∈labels,Supported x.G)
      (τ : GLabel Θ mesh U→Character) (χ : GLabel Θ mesh U→RayCharacter)
      (t θ X : GLabel Θ mesh U→ℝ) (V : GLabel Θ mesh U→ℝ→ℂ)
      (hc : ∀x,HasCompactSupport (V x)) (hs : ∀x,ContDiff ℝ ∞ (V x))
      (H Mmin Mmax εframe A A₀ c u' Lf err : ℝ)
      (adm : Second.AdmissibleGroup (gFrame frameL Θ mesh η U) Mmin Mmax mesh εframe U gr labels H),
      2 ≤ U → mesh ≤ 1 → 0 ≤ mesh → 0 ≤ A →
      A₀ ≤ 9179599/10000000 → u' ≤ (QRH.SourceCertificate.u:ℝ) →
      gr.colLog ≤ A₀-c-u'+err → 1-6*u' ≤ H+err →
      max 0 (115/1000-c) ≤ Real.logb U (max 1 Lf)+err →
      (∀x∈labels,∀z∈rows x,Fits η gr x ∧ z ≠ 0 ∧
        CenteredExceptionalProfile.FixedInducingRow (x.char gr) Q m 1 z) →
      (∀x∈labels,0 ≤ rowWeight x) →
      (∀x∈labels,rowWeight x*(sourceVolume (src x))^2*
        (sourcePrefix (src x) x.G x.D*max 1 (src x).L)⁻¹=
          gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹) →
      (∀x∈labels,Squarefree x.D) →
      (∀x∈labels,(x.G.absNorm:ℝ) ≤ U^Bcap) → (∀x∈labels,(x.D.absNorm:ℝ) ≤ U^Bcap) →
      (∀x∈labels,∀ B':commonAlloc (src x) x.G,∀ E:fullPrimaryAlloc (src x) x.G B' x.D,
        ((src x).Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*(src x).P i.val.val)*
          ((src x).R.absNorm:ℝ)*(x.G.absNorm:ℝ)*(x.D.absNorm:ℝ) ≤ U^Bcap) →
      (∀x∈labels,x.char gr=childCharacter (τ x) (χ x) ∧ m=nativeSourceMask (src x)) →
      (∀x∈labels,∀z∈rows x,
        (HeckeRowClosure.rowConductorBound (x.char gr) m 1 z:ℝ) ≤ U^Bcap) →
      (∀x∈labels,0<X x) →
      (∀x∈labels,C*fixedMarkCost (src x)*
        (sourceControl S (src x).W₁*sourceControl S (src x).W₂)^2*U^ε*
        profileHeightCost (src x) (t x) (θ x) J*(windowMass (V x) (hc x) (hs x) J)^2 ≤ A) →
      let energy := fun x z=>if hx:x∈labels then
        rowWeight x*(‖fixedWindowRow (src x) ha ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D
          (t x) (θ x) (X x) (V x) z‖^2*(ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re) else 0
      (∑x∈labels,gWeight x*(prefixNorm x*gr.norm*(∑z∈rows x,energy x z))) ≤ 
        (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*A*
          U^(gr.colLog+gr.twistLog+u'-(3036/100000)+3*mesh+Real.logb U 2+(17/6)*err+εframe/8) := by
  obtain ⟨J,S,hS,h⟩ := original_window_H15_subpower (ι:=Fin Θ.N) ha hb ω₁ ω₂ Θ.N (by simp) ε Bcap hε hBcap
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hbound⟩ := h Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro mesh gr η hQ₀ hQt hQ72 m hm hlam ht labels rows src rowWeight hG τ χ t θ X V hc hs
    H Mmin Mmax εframe A A₀ c u' Lf err adm hU₂ hmsh hmesh hA hroot hu hcol hfill hmin
    num hweight hscale hD hNG hND hbudget hchar hcond hX hpay
  let E : GLabel Θ mesh U→O→ℝ := fun x z=>if hx:x∈labels then
    rowWeight x*(‖fixedWindowRow (src x) ha ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D
      (t x) (θ x) (X x) (V x) z‖^2*(ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re) else 0
  let rows' := fun x=>(rows x).filter (fun z=>(ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re ≠ 0)
  change (∑x∈labels,gWeight x*(prefixNorm x*gr.norm*(∑z∈rows x,E x z))) ≤ _
  have heq : (∑x∈labels,gWeight x*(prefixNorm x*gr.norm*(∑z∈rows x,E x z))) =
      ∑x∈labels,gWeight x*(prefixNorm x*gr.norm*(∑z∈rows' x,E x z)) := by
    apply Finset.sum_congr rfl
    intro x hx
    congr 2
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hn
    have hp : (ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re = 0 := by
      by_contra hp
      exact hn (Finset.mem_filter.mpr ⟨hz,hp⟩)
    simp only [E,dif_pos hx,hp,mul_zero]
  rw [heq]
  apply fixed_filled_admissible gr η Q hQ₀ hQt hQ72 m hm hlam ht labels rows' E H Mmin Mmax εframe A A₀ c u' Lf err
    adm hU₂ hmsh hA hroot hu hcol hfill hmesh hmin
    (fun x hx z hz=>num x hx z (Finset.mem_filter.mp hz).1)
    (fun x hx z hz=>fixed_ball_support z (x.n 1) (Finset.mem_filter.mp hz).2)
  intro x hx z hz'
  have hz := (Finset.mem_filter.mp hz').1
  dsimp only [E]
  rw [dif_pos hx]
  let D := fixedDatum (x.char gr) Q m 1 z hQ₀ hm one_ne_zero (num x hx z hz).2.1 hlam ht (num x hx z hz).2.2
  have hh := hU.2 (src x) D rfl (by simpa only [D,fixedDatum,one_mul] using hcond x hx z hz)
    x.G x.D (hG x hx) (hD x hx) (hNG x hx) (hND x hx) (hbudget x hx)
    (τ x) (χ x) (hchar x hx).1 (hchar x hx).2 (t x) (θ x) (X x) (hX x hx) (V x) (hc x) (hs x)
  let K := C*fixedMarkCost (src x)*(sourceControl S (src x).W₁*sourceControl S (src x).W₂)^2*U^ε*
    profileHeightCost (src x) (t x) (θ x) J*(windowMass (V x) (hc x) (hs x) J)^2
  have hh' : ‖fixedWindowRow (src x) ha ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D (t x) (θ x) (X x) (V x) z‖^2 ≤ 
      K*(sourceVolume (src x))^2*(sourcePrefix (src x) x.G x.D*max 1 (src x).L)⁻¹ := by
    exact hh.trans_eq (by dsimp only [K];ring)
  have hw : 0 ≤ gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹ := by unfold prefixNorm;positivity
  calc
    _  ≤  rowWeight x*‖fixedWindowRow (src x) ha ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D (t x) (θ x) (X x) (V x) z‖^2 :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (ballProfile_le_one _)) (hweight x hx)
    _  ≤  rowWeight x*(K*(sourceVolume (src x))^2*(sourcePrefix (src x) x.G x.D*max 1 (src x).L)⁻¹) :=
      mul_le_mul_of_nonneg_left hh' (hweight x hx)
    _ = K*(gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹) := by rw [←hscale x hx];ring
    _  ≤  A*(gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹) := mul_le_mul_of_nonneg_right (hpay x hx) hw
    _ = _ := by rw [div_eq_mul_inv];ring

#print axioms native_fixed_window_filled
end QRH.Cycle092.FixedFourierH15
