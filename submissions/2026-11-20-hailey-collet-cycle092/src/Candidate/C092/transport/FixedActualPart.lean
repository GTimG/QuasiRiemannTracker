/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed H.5 price on the genuine active colored second Poisson sum. -/
import Candidate.C092.transport.FixedActualSplitBudget
import Candidate.C092.transport.ActualLabelFiniteCostsSupply
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource CenteredMomentSecondWindowBudget
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows Packet Packet.Grouped
open Second.ConcreteFrame Second.ConcreteGroup Second.ConcreteLabelAssembly Second.Concrete
open QRH.Cycle092.SignedCenter QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFourierH15
open QRH.Cycle092.PairedRetainedBudget
namespace QRH.Cycle092.FixedFrameSeam
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L:ℝ}

theorem fixed_part (θ:GData L) (η ω₁ ω₂:Character) (N:ℕ) (hN:θ.N  ≤  N)
    (Bmask mesh ε εg δ:ℝ) (hm:θ.Bmask  ≤  Bmask) (hb:24  ≤  θ.Bmask)
    (hmesh:0 < mesh) (hm1:mesh  ≤  1) (hε:0<ε) (hεg:0<εg) (hδ:0<δ) :
    ∃ J:ℕ,∃ S:Finset (ℕ×ℕ),(0,0)∈S ∧ ∃ Cg:ℝ,0 ≤ Cg ∧ ∀Q:Id,∃ C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,
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
    RootColoredSeed.groupedPartTerms true s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂) (childCharacter P.base ξ)
      χ₀ Q m t Kc Tsec Z ξr H  ≤ 
      (classLambda 1 Cg 1 Cb θ.a J*Z^δ*rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*J) := by
  obtain ⟨J,S,hS,Cg,hCg,hseries⟩:=actual_split_price θ η ω₁ ω₂ N hN Bmask mesh ε εg hm hb hmesh hm1 hε hεg
  obtain ⟨Cf,hCf,hfin⟩:=ActualLabelFiniteCosts.actual_window_finite_costs δ hδ
  refine ⟨J,S,hS,Cf*Cg,mul_nonneg hCf.le hCg,?_⟩
  intro Q;obtain ⟨C,hC,h⟩:=hseries Q
  refine ⟨C,hC,?_⟩
  filter_upwards [h,hfin] with Z hz hf
  refine ⟨hz.1,?_⟩
  intro C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hFhole hH hR hcap hP
    hQ₀ hQt hQ72 hQi m hmn hl ht t Kc Tsec ξr H A₀ c u' err hroot hu hcol hfill hlo hhi hmin hfee hK hklog hcut hk8 hk2 ht0 hts hξ hH8
  obtain ⟨Mm,B,_,_,_,_,hcm,hmult,hbox⟩:=hf.2 s θ.ha0 ω₁ ω₂ hcap Kc Tsec ξr H hk8 hk2 ht0 hts hξ hH8
  have hh:=hz.2 C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hFhole hH hR
    hcap hP hQ₀ hQt hQ72 hQi m hmn hl ht t Kc Tsec ξr H A₀ c u' err B Mm hroot hu hcol hfill hlo hhi hmin hfee hK hklog hcut hbox hmult
  apply hh.trans
  let A:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    C*fixedMarkCost s*(sourceControl S s.W₁*sourceControl S s.W₂)^2*(2+‖s.t₁‖+‖s.t₂‖)^(2*J)
  have hA:0≤A:=by dsimp [A];have:=fixedMarkCost_nonneg s;positivity
  have hζ:=Real.rpow_nonneg (zero_lt_one.trans rs.hZ).le u'
  have w:=windowHeightConstant_nonneg J
  have hmul:=mul_le_mul_of_nonneg_right hcm (show 0 ≤ Cg*A*windowHeightConstant J/θ.a^2*
    rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ)*(1+‖t‖)^(2*J) by positivity)
  change classLambda _ Cg _ A θ.a J*rs.vol^2*Z^u'*_*_ ≤ classLambda 1 (Cf*Cg) 1 A θ.a J*Z^δ*rs.vol^2*Z^u'*_*_
  unfold classLambda
  convert hmul using 1 <;> ring

#print axioms fixed_part
end QRH.Cycle092.FixedFrameSeam
