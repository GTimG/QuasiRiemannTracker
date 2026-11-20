/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite bank of fixed physical prices, produced by native H.15
and numerical B0 before actual restored families or positive root fees. -/
import Candidate.C092.transport.FixedActualPart
import Candidate.C092.transport.ActualStageFrameBudgetData
import Candidate.C092.transport.ActualStageFrameBudgetFee
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

/-- Exact output of the native fixed physical theorem. Every geometry gate
is primitive; there is no assumed frame energy, H15 or retained budget. -/
def FixedPartAt (θ:GData L)(η ω₁ ω₂:Character)(mesh ε εg δ:ℝ)
    (J:ℕ)(S:Finset (ℕ×ℕ))(Cg:ℝ)(Q:Id)(C Z:ℝ) : Prop :=
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
      (classLambda 1 Cg 1 Cb θ.a J*Z^δ*rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*J)

/-- All genuine fixed analytic work is done by fixed_part. -/
theorem fixed_native_packet (θ:GData L)(η ω₁ ω₂:Character)(N:ℕ)(hN:θ.N ≤ N)
    (Bmask mesh ε εg δ:ℝ)(hm:θ.Bmask ≤ Bmask)(hb:24 ≤ θ.Bmask)
    (hmesh:0 < mesh)(hm1:mesh ≤ 1)(hε:0<ε)(hεg:0<εg)(hδ:0<δ) :
    ∃J:ℕ,∃S:Finset (ℕ×ℕ),(0,0)∈S ∧ ∃Cg:ℝ,0 ≤ Cg ∧ ∀Q:Id,∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,FixedPartAt θ η ω₁ ω₂ mesh ε εg δ J S Cg Q C Z :=
  fixed_part θ η ω₁ ω₂ N hN Bmask mesh ε εg δ hm hb hmesh hm1 hε hεg hδ

/-- The surviving slot count is finite, including zero. The actual Q is
fixed from the original ray/base/colors before this native bank and Z. -/
theorem actual_fixed_bank (N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
    (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base:Character)(Q:Id)(hQ:Q ≤ rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
    (hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ base.modulus)
    (η ω₁ ω₂:Character)(mesh ε εg δ:ℝ)
    (hmesh:0 < mesh)(hm1:mesh ≤ 1)(hε:0<ε)(hεg:0<εg)(hδ:0<δ) :
    ∃j:Fin (N+1)→ℕ,∃S:Fin (N+1)→Finset (ℕ×ℕ),∃Cg C:Fin (N+1)→ℝ,
      (∀k,(0,0)∈S k ∧ 0 ≤ Cg k ∧ 0<C k) ∧ ∀ᶠZ:ℝ in atTop,∀k:Fin (N+1),
      FixedPartAt (frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase)
        η ω₁ ω₂ mesh ε εg δ (j k) (S k) (Cg k) Q (C k) Z := by
  have hh (k:Fin (N+1)):=fixed_native_packet
    (frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase)
    η ω₁ ω₂ N (Nat.le_of_lt_succ k.isLt) 24 mesh ε εg δ le_rfl le_rfl hmesh hm1 hε hεg hδ
  choose j S hS Cg hCg hp using hh
  choose C hC hev using fun k=>hp k Q
  exact ⟨j,S,Cg,C,fun k=>⟨hS k,hCg k,hC k⟩,Filter.eventually_all.mpr hev⟩

#print axioms fixed_native_packet
#print axioms actual_fixed_bank
end
end QRH.Cycle092.ActualStageFrameBudget
