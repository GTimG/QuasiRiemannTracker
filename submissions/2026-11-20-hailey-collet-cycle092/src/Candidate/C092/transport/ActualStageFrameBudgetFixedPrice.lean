/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite bank of fixed physical prices, produced by native H.15
and numerical B0 before actual restored families or positive root fees. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedBank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource CenteredMomentSecondWindowBudget
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows Packet Packet.Grouped
open Second.ConcreteFrame Second.ConcreteGroup Second.ConcreteLabelAssembly Second.Concrete
open QRH.Cycle092.SignedCenter QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFourierH15
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.FixedFrameSeam
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {L:ℝ}

/-- Native fixed physical price with a common early homogeneous fee. -/
def FixedGlobalAt (θ:GData L)(η ω₁ ω₂:Character)(mesh ε εg δ:ℝ)
    (J:ℕ)(S:Finset (ℕ×ℕ))(Cg:ℝ)(Q:Id)(C Z:ℝ)
    (Jglobal degree:ℕ)(controls:Finset (ℕ×ℕ))(Cfee Kslot:ℝ) : Prop :=
2 ≤ Z ∧ ∀ (C₀ D₀:Id) (hc₀:Supported C₀) (E₀:Finset (CenteredMomentCanonicalFirst.CommonIndex C₀ D₀))
      (ξ₁ ξ₂:RayCharacter) (F:FixedPair η C₀ D₀ hc₀ E₀ ξ₁ ξ₂) (P:SidePack η)
      (ξ χ₀:RayCharacter) (s:Source (Fin θ.N) θ.a θ.b) (rs:GSrc θ mesh Z),
    (P.base=F.left ∨ P.base=F.right) → (C₀.absNorm:ℝ) ≤ Z^(8:ℝ) →
    rs.W₁=s.W₁ → rs.W₂=s.W₂ → rs.t₁=s.t₁/(2*Real.pi) → rs.t₂=s.t₂/(2*Real.pi) →
    rs.X₁=s.X₁ → rs.X₂=s.X₂ → rs.Y₁=s.Y₁ → rs.Y₂=s.Y₂ →
    Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d →
    rs.V₀=P.V → P.Cs∣s.R → s.Fhole=1 → s.H=∅ → (s.R.absNorm:ℝ) ≤ Z^(8:ℝ) →
    (∀I∈RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ) ≤ Z^(8:ℝ)) →
    (∀i,s.P i ≤ Z) → Q≠0 → Q≠⊤ → Q ≤ Ideal.span {(72:O)} → internalQ θ.Q θ.η₀=Q →
    ∀ (m:O),m≠0 → goodLambda∣m → (2:O)∣m →
    ∀ (t Kc Tsec ξr H A₀ c u' err:ℝ),
    A₀ ≤ 9179599/10000000 → u' ≤ (QRH.SourceCertificate.u:ℝ) →
    rs.colLog ≤ A₀-c-u'+err → 1-6*u' ≤ commonH rs+err → 0 ≤ commonH rs → commonH rs ≤ 19/10 →
    max 0 (115/1000-c) ≤ Real.logb Z (max 1 s.L)+err →
    ε+3*mesh+Real.logb Z 2+(17/6)*err+εg/8 ≤ 3036/100000 →
    0<Kc → Z^rs.kLog=Kc → 32*frequencyRadius Tsec Z ξr ≤ Z^cutoffLog rs →
    8 ≤ Kc → Kc ≤ Z^(2:ℝ) → 0 ≤ Tsec → Tsec ≤ Z^(2:ℝ) → ξr ≤ 1 → H ≤ Z^(8:ℝ) →
    let ctl:=sourceControl S s.W₁*sourceControl S s.W₂
    let Cb:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
      C*fixedMarkCost s*ctl^2*(2+‖s.t₁‖+‖s.t₂‖)^(2*J)
    ∀height:ℝ,0 ≤ height → (∀i,s.M i ≤ Kslot) →
    RootColoredSeed.groupedPartTerms true s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂) (childCharacter P.base ξ)
      χ₀ Q m t Kc Tsec Z ξr H ≤
      (Cfee*(sourceControl controls s.W₁*sourceControl controls s.W₂)^2*
        (1+‖s.t₁‖+‖s.t₂‖+height)^degree*Z^δ*rs.vol^2*Z^u'*
          ((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*Jglobal)

/-- Only a numerical Cb bound is needed to normalize the authentic
native fixed packet. The original physical source and class sum remain exact. -/
theorem fixed_global_of_packet (θ:GData L)(η ω₁ ω₂:Character)(mesh ε εg δ:ℝ)
    (J:ℕ)(S:Finset (ℕ×ℕ))(Cg:ℝ)(Q:Id)(C Z:ℝ)
    (Jglobal degree:ℕ)(controls:Finset (ℕ×ℕ))(Cfee Kslot:ℝ)
    (hCg:0 ≤ Cg)(hC:0 ≤ C)(hCfee:0 ≤ Cfee)(hJ:J ≤ Jglobal)
    (packet:FixedPartAt θ η ω₁ ω₂ mesh ε εg δ J S Cg Q C Z)
    (fee:∀s:Source (Fin θ.N) θ.a θ.b,(∀i,s.M i ≤ Kslot) → ∀height:ℝ,0 ≤ height →
      let Cb:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
        C*fixedMarkCost s*(sourceControl S s.W₁*sourceControl S s.W₂)^2*(2+‖s.t₁‖+‖s.t₂‖)^(2*J)
      classLambda 1 Cg 1 Cb θ.a J ≤ Cfee*(sourceControl controls s.W₁*sourceControl controls s.W₂)^2*
        (1+‖s.t₁‖+‖s.t₂‖+height)^degree) :
    FixedGlobalAt θ η ω₁ ω₂ mesh ε εg δ J S Cg Q C Z Jglobal degree controls Cfee Kslot := by
  refine ⟨packet.1,?_⟩
  intro C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hFhole hH hR hcap hP
    hQ₀ hQt hQ72 hQi m hmn hl ht t Kc Tsec ξr H A₀ c u' err hroot hu hcol hfill hlo hhi hmin hfee hK hklog hcut hk8 hk2 ht0 hts hξ hH8
  dsimp only
  intro height hh hMarks
  have hn:=packet.2 C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hFhole hH hR hcap hP
    hQ₀ hQt hQ72 hQi m hmn hl ht t Kc Tsec ξr H A₀ c u' err hroot hu hcol hfill hlo hhi hmin hfee hK hklog hcut hk8 hk2 ht0 hts hξ hH8
  have hf:=fee s hMarks height hh
  have hz:0<Z:=zero_lt_one.trans rs.hZ
  have hpow:(1+‖t‖)^(2*J) ≤ (1+‖t‖)^(2*Jglobal):=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.mul_le_mul_left 2 hJ)
  have hscale:0 ≤ Z^δ*rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ):=by positivity
  have hscaled:=mul_le_mul_of_nonneg_right hf hscale
  have h1:=mul_le_mul_of_nonneg_right hscaled (show (0:ℝ) ≤ (1+‖t‖)^(2*J) by positivity)
  have hcoef:0 ≤ Cfee*(sourceControl controls s.W₁*sourceControl controls s.W₂)^2*
      (1+‖s.t₁‖+‖s.t₂‖+height)^degree*Z^δ*rs.vol^2*Z^u'*
        ((Ideal.span {rs.V₀}).absNorm:ℝ):=by positivity
  apply hn.trans
  apply (le_of_eq (by ring)).trans (h1.trans ?_)
  exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hpow hcoef)

#print axioms fixed_global_of_packet
end
end QRH.Cycle092.ActualStageFrameBudget
