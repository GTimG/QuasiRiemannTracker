/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed H.5 price on the genuine active colored second Poisson sum. -/
import Candidate.C092.transport.FixedClassActualSeam
import Candidate.C092.transport.PairedRetainedBudgetLambda
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

theorem actual_split_price (θ:GData L) (η ω₁ ω₂:Character) (N:ℕ) (hN:θ.N  ≤  N)
    (Bmask mesh ε εg:ℝ) (hm:θ.Bmask  ≤  Bmask) (hb:24  ≤  θ.Bmask)
    (hmesh:0 < mesh) (hm1:mesh  ≤  1) (hε:0<ε) (hεg:0<εg) :
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
    ∀ (t Kc Tsec ξr H A₀ c u' err:ℝ) (B:ℤ) (Mm:ℕ),
    A₀ ≤ 9179599/10000000 → u' ≤ (QRH.SourceCertificate.u:ℝ) →
    rs.colLog ≤ A₀-c-u'+err → 1-6*u' ≤ commonH rs+err → 0 ≤ commonH rs → commonH rs ≤ 19/10 →
    max 0 (115/1000-c) ≤ Real.logb Z (max 1 s.L)+err →
    ε+3*mesh+Real.logb Z 2+(17/6)*err+εg/8 ≤ 3036/100000 →
    0<Kc → Z^rs.kLog=Kc → 32*frequencyRadius Tsec Z ξr ≤ Z^cutoffLog rs →
    let carrier:=RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂)
    (∀l n,inRange carrier Kc (frequencyRadius Tsec Z ξr) H l n → n∈box B) →
    (∀g:Lab carrier→Id,IsColumn carrier g → ∀G A,
      ((Finset.univ:Finset (Lab carrier)).filter (fun l=>g l=G ∧ lA carrier l=A)).card ≤ Mm) →
    let ctl:=sourceControl S s.W₁*sourceControl S s.W₂
    let Cb:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
      C*fixedMarkCost s*ctl^2*(2+‖s.t₁‖+‖s.t₂‖)^(2*J)
    RootColoredSeed.groupedPartTerms true s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂) (childCharacter P.base ξ)
      χ₀ Q m t Kc Tsec Z ξr H  ≤ 
      (classLambda ((box B).card:ℝ) Cg Mm Cb θ.a J*rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*J) := by
  obtain ⟨J,S,hS,h0⟩:=actual_class_series θ η ω₁ ω₂ N hN Bmask mesh ε εg hm hb hmesh hm1 hε hεg
  obtain ⟨Cg,hCg,hsplit⟩:=FixedPhysicalClassLedger.actual_split_bound J
  refine ⟨J,S,hS,Cg,hCg,?_⟩
  intro Q;obtain ⟨C,hC,hZ⟩:=h0 Q
  refine ⟨C,hC,hZ.mono ?_⟩
  intro Z hz;refine ⟨hz.1,?_⟩
  intro C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hFhole hH hR hcap hP
    hQ₀ hQt hQ72 hQi m hmn hl ht t Kc Tsec ξr H A₀ c u' err B Mm hroot hu hcol hfill hlo hhi hmin hfee hK hklog hcut
  dsimp only
  intro hbox hmult
  let ctl:=sourceControl S s.W₁*sourceControl S s.W₂
  let Cb:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    C*fixedMarkCost s*ctl^2*(2+‖s.t₁‖+‖s.t₂‖)^(2*J)
  have hCb:0 ≤ Cb:=by dsimp [Cb];have:=fixedMarkCost_nonneg s;positivity
  have hv:=rs.vol_pos (zero_lt_one.trans rs.hZ)
  have hzu:=Real.rpow_pos_of_pos (zero_lt_one.trans rs.hZ) u'
  let B0:=Cb*rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Z^u'
  have hB0:0 ≤ B0:=by dsimp [B0];positivity
  have hr : ∀i,∀P∈s.H,P.val∈rs.R₀ i := by simp [hH]
  have hsH : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap) := by simp [hH]
  have hbud:(s.R.absNorm:ℝ)*(Z^(8:ℝ))^2*((∏I∈holes s.H,I).absNorm:ℝ) ≤ Z^θ.Bmask := by
    rw [hH];simp only [holes,Finset.image_empty,Finset.prod_empty,map_one,Nat.cast_one,mul_one]
    calc
      _  ≤  Z^(8:ℝ)*(Z^(8:ℝ))^2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
      _ = Z^(24:ℝ) := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans rs.hZ).le,←Real.rpow_add (zero_lt_one.trans rs.hZ)];norm_num
      _  ≤  _ := Real.rpow_le_rpow_of_exponent_le rs.hZ.le hb
  apply lambda_of_class_bound _ _ Cg rs.vol Mm B0 Cb _ (Z^u') θ.a t J
    (by positivity) hCg hv.le (by positivity) hCb (by positivity) hzu.le le_rfl
  apply hsplit P ξ Q m hmn hl ht hQ72 hQi χ₀ s θ.ha0 ω₁ ω₂ rs hW₁ hW₂ ht₁ ht₂
    hX₁ hX₂ hY₁ hY₂ hV₀ hCR hcan t Kc (frequencyRadius Tsec Z ξr) H B hK hklog hcut
    hbox hsH hr (Z^(8:ℝ)) hcap hbud Mm hmult B0 hB0
  intro n hn g hg χ v
  exact hz.2 C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hX₁ hX₂ hcan hV₀ hCR hFhole hH hR hcap hP
    hQ₀ hQt hQ72 m t Kc (frequencyRadius Tsec Z ξr) H g hg n χ v A₀ c u' err
    hroot hu hcol hfill hlo hhi hmin hfee

#print axioms actual_split_price
end QRH.Cycle092.FixedFrameSeam
