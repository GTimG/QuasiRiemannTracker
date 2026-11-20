/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual fixed window rows enter the original native packed frame price.
Only identifying equalities and explicit scalar profile/window debits remain. -/
import Candidate.C092.transport.FixedFourierH15Subpower
import Candidate.C092.transport.FixedFramePrice

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
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFramePacking
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {frameL : ℝ} (Θ : GData frameL)
local instance c092LocalInst_Candidate_C092_transport_FixedFourierH15Packing_2e9497e351696ac8_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- The numerical H15 is supplied by the genuine source theorem, rather than
assumed. Scalar debits include every marked-profile, height and Fourier cost.
Data equalities identify the actual native row. The scalar ledger retains
the shortened source volume, original prefix and cutoff before pricing. -/
theorem native_fixed_window_price (ha : 0<Θ.a) (hb : 0 ≤ Θ.b) (ω₁ ω₂ : Character)
    (ε Bcap : ℝ) (hε : 0<ε) (hBcap : 0 ≤ Bcap) :
    ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),∃ hS : (0,0)∈S,
    ∀ Q : Id,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀ (mesh : ℝ) (gr : GSrc Θ mesh U) (η : Character)
      (hQ₀ : Q≠0) (hQt : Q≠⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
      (m : O) (hm : m≠0) (hlam : ConcretePrimeRowBridge.goodLambda∣m) (ht : (2:O)∣m)
      (labels : Finset (GLabel Θ mesh U)) (fit : ∀ x∈labels,Fits η gr x)
      (rows : GLabel Θ mesh U→Finset O)
      (src : GLabel Θ mesh U→Source (Fin Θ.N) Θ.a Θ.b)
      (rowWeight : GLabel Θ mesh U→ℝ)
      (dat : ∀ x∈labels,∀ z∈rows x,FixedCubeDatum)
      (hG : ∀ x∈labels,Supported x.G)
      (τ : GLabel Θ mesh U→Character) (χ : GLabel Θ mesh U→RayCharacter)
      (t θ X : GLabel Θ mesh U→ℝ) (V : GLabel Θ mesh U→ℝ→ℂ)
      (hc : ∀x,HasCompactSupport (V x)) (hs : ∀x,ContDiff ℝ ∞ (V x))
      (A B M Lf : ℝ),0 ≤ A → 0 ≤ B →
      (∀x∈labels,0 ≤ rowWeight x) →
      (∀x∈labels,rowWeight x*(sourceVolume (src x))^2*
        (sourcePrefix (src x) x.G x.D*max 1 (src x).L)⁻¹=
          gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹) →
      (∀x∈labels,Squarefree x.D) → (∀x∈labels,(x.G.absNorm:ℝ) ≤ U^Bcap) →
      (∀x∈labels,(x.D.absNorm:ℝ) ≤ U^Bcap) → (∀x∈labels,0<X x) →
      (∀x∈labels,∀z∈rows x,∀ B':commonAlloc (src x) x.G,∀ E:fullPrimaryAlloc (src x) x.G B' x.D,
        ((src x).Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*(src x).P i.val.val)*
          ((src x).R.absNorm:ℝ)*(x.G.absNorm:ℝ)*(x.D.absNorm:ℝ) ≤ U^Bcap) →
      (∀x hx z hz,(dat x hx z hz).Q=Q ∧ (dat x hx z hz).m=m ∧
        (dat x hx z hz).A=1 ∧ (dat x hx z hz).z=z ∧ (dat x hx z hz).η=x.char gr ∧
        (dat x hx z hz).η=childCharacter (τ x) (χ x) ∧
        (dat x hx z hz).m=nativeSourceMask (src x) ∧
        (HeckeRowClosure.rowConductorBound (dat x hx z hz).η (dat x hx z hz).m 1
          ((dat x hx z hz).A*(dat x hx z hz).z):ℝ) ≤ U^Bcap) →
      (∀x∈labels,C*fixedMarkCost (src x)*
        (sourceControl S (src x).W₁*sourceControl S (src x).W₂)^2*U^ε*
        profileHeightCost (src x) (t x) (θ x) J*(windowMass (V x) (hc x) (hs x) J)^2 ≤ A) →
      (∀y:O,y≠0 → ((Ideal.span {y}).absNorm:ℝ) ≤ U^M →
        ∑x∈labels.filter (fun x=>x.twist∣y),gWeight x ≤ B) →
      (∀x∈labels,∀z∈rows x,((Ideal.span {(gr.V₀*x.twist)*z}).absNorm:ℝ) ≤ U^M) →
      let energy := fun x z=>if hx:x∈labels then if hz:z∈rows x then
        rowWeight x*(‖nativeWindowPolynomial (src x) ha (dat x hx z hz) ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D
          (t x) (θ x) (X x) (V x)‖^2*(ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re) else 0 else 0
      (∑x∈labels,gWeight x*(prefixNorm x*gr.norm*(∑z∈rows x,energy x z))) ≤
        (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
          A*B*U^(gr.kLog+M/6)/max 1 Lf := by
  obtain ⟨J,S,hS,h⟩ := original_window_H15_subpower (ι:=Fin Θ.N) ha hb ω₁ ω₂ Θ.N (by simp) ε Bcap hε hBcap
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hbound⟩ := h Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro mesh gr η hQ₀ hQt hQ72 m hm hlam ht labels fit rows src rowWeight dat hG τ χ t θ X V hc hs
    A B M Lf hA hB hweight hscale hD hNG hND hX hbudget hdat hpay hfib hcap
  dsimp only
  refine native_fixed_price gr η Q hQ₀ hQt hQ72 m hm hlam ht labels fit rows _ A B M Lf hA hB hfib ?_ hcap ?_
  · intro x hx z hz
    obtain ⟨hQ,hdm,hda,hdz,hde,hη,hsourcem,hcond⟩ := hdat x hx z hz
    refine ⟨hdz ▸ (dat x hx z hz).hz,?_⟩
    simpa only [hQ,hde,hdm,hda,hdz] using (dat x hx z hz).fixed
  · intro x hx z hz
    rw [dif_pos hx,dif_pos hz]
    obtain ⟨hQ,hdm,hda,hdz,hde,hη,hsourcem,hcond⟩ := hdat x hx z hz
    have hh := hU.2 (src x) (dat x hx z hz) hQ hcond x.G x.D (hG x hx) (hD x hx)
      (hNG x hx) (hND x hx) (hbudget x hx z hz) (τ x) (χ x) hη hsourcem
      (t x) (θ x) (X x) (hX x hx) (V x) (hc x) (hs x)
    let K : ℝ := C*fixedMarkCost (src x)*(sourceControl S (src x).W₁*sourceControl S (src x).W₂)^2*U^ε*profileHeightCost (src x) (t x) (θ x) J*(windowMass (V x) (hc x) (hs x) J)^2
    have hh' : ‖nativeWindowPolynomial (src x) ha (dat x hx z hz) ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D (t x) (θ x) (X x) (V x)‖^2 ≤
        K*(sourceVolume (src x))^2*(sourcePrefix (src x) x.G x.D*max 1 (src x).L)⁻¹ :=
      hh.trans_eq (by dsimp only [K];ring)
    have hp : 0 ≤ prefixNorm x := by unfold prefixNorm;positivity
    have hw : 0 ≤ gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹ := by positivity
    calc
      _ ≤ rowWeight x*‖nativeWindowPolynomial (src x) ha (dat x hx z hz) ω₁ ω₂ (τ x) (χ x) x.G (hG x hx) x.D (t x) (θ x) (X x) (V x)‖^2 :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (ballProfile_le_one _)) (hweight x hx)
      _ ≤ rowWeight x*(K*(sourceVolume (src x))^2*(sourcePrefix (src x) x.G x.D*max 1 (src x).L)⁻¹) :=
        mul_le_mul_of_nonneg_left hh' (hweight x hx)
      _ = K*(gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹) := by rw [←hscale x hx];ring
      _ ≤ A*(gr.vol^2*(prefixNorm x*max 1 Lf)⁻¹) := mul_le_mul_of_nonneg_right (hpay x hx) hw
      _ = _ := by rw [div_eq_mul_inv];ring

#print axioms native_fixed_window_price
end QRH.Cycle092.FixedFourierH15
