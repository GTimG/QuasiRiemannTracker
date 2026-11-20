/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native fixed seam on the actual second class. Admissibility, support of the
common ideal, the per-row H15 datum and its conductor all come from that class. -/
import Candidate.C092.transport.FixedFrameB0
import Candidate.C092.transport.FixedFrameConductorCapsRowData
import Candidate.C092.transport.FixedFrameConductorCapsUniform
import Candidate.C092.transport.ColoredFrameAdmissibleActual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentChildRows CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectors CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair MixedPrincipalWindow
open Packet Packet.Grouped Second.ConcreteFrame Second.ConcreteGroup Second.ConcreteLabelAssembly
open CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional CenteredMomentFirstPhysicalSource
open QRH.Cycle092.SignedCenter QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFourierH15
open QRH.Cycle092.FixedFramePacking QRH.Cycle092.FixedFrameConductorCaps
namespace QRH.Cycle092.FixedFrameSeam
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L:ℝ}

theorem actual_class_series (θ:GData L) (η ω₁ ω₂:Character) (N:ℕ) (hN:θ.N ≤ N)
    (Bmask mesh ε εg:ℝ) (hm:θ.Bmask ≤ Bmask) (hb:24 ≤ θ.Bmask)
    (hmesh:0 < mesh) (hm1:mesh ≤ 1) (hε:0<ε) (hεg:0<εg) :
    ∃ J:ℕ,∃ S:Finset (ℕ×ℕ),(0,0)∈S ∧ ∀Q:Id,∃ C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,
    2 ≤ Z ∧ ∀ (C₀ D₀:Id) (hc₀:Supported C₀) (E₀:Finset (CenteredMomentCanonicalFirst.CommonIndex C₀ D₀))
      (ξ₁ ξ₂:RayCharacter) (F:FixedPair η C₀ D₀ hc₀ E₀ ξ₁ ξ₂) (P:SidePack η)
      (ξ χ₀:RayCharacter) (s:Source (Fin θ.N) θ.a θ.b) (rs:GSrc θ mesh Z),
    (P.base=F.left ∨ P.base=F.right) → (C₀.absNorm:ℝ) ≤ Z^(8:ℝ) →
    rs.X₁=s.X₁ → rs.X₂=s.X₂ → Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d →
    rs.V₀=P.V → P.Cs∣s.R → s.Fhole=1 → s.H=∅ → (s.R.absNorm:ℝ) ≤ Z^(8:ℝ) →
    (∀I∈RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ) ≤ Z^(8:ℝ)) →
    (∀i,s.P i ≤ Z) → Q≠0 → Q≠⊤ → Q ≤ Ideal.span {(72:O)} →
    ∀ (m:O) (t Kc R radius:ℝ) (g:Lab (RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂))→Id),
    IsColumn (RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂)) g →
    ∀ (n:Fin 4→ℤ) (χ:RayCharacter) (v A₀ c u' err:ℝ),
    A₀ ≤ 9179599/10000000 → u' ≤ (QRH.SourceCertificate.u:ℝ) →
    rs.colLog ≤ A₀-c-u'+err → 1-6*u' ≤ commonH rs+err →
    0 ≤ commonH rs → commonH rs ≤ 19/10 →
    max 0 (115/1000-c) ≤ Real.logb Z (max 1 s.L)+err →
    ε+3*mesh+Real.logb Z 2+(17/6)*err+εg/8 ≤ 3036/100000 →
    let labs:=FixedPhysicalClassLedger.actualFrameLabels η s θ.ha0 ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R radius rs P.j₀ ξ g n χ
    let pCtl:=sourceControl S s.W₁*sourceControl S s.W₂
    let B0:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
      C*fixedMarkCost s*pCtl^2*(2+‖s.t₁‖+‖s.t₂‖)^(2*J)*
      rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Z^u'
    ∑ x∈labs,gWeight x*FixedPhysicalClassLedger.gEnergy s θ.ha0 ω₁ ω₂ η rs Q x v ≤ B0*(1+‖v‖)^(2*J) := by
  let Bcap:=uniformExponent N Bmask
  have h27:27 ≤ Bcap:=by
    dsimp [Bcap,uniformExponent];have:=Nat.cast_nonneg (α:=ℝ) N;linarith
  obtain ⟨J,S,hS,hser⟩:=full_fixed_series θ ω₁ ω₂ N hN ε Bcap hε (by linarith)
  refine ⟨J,S,hS,?_⟩
  intro Q;obtain ⟨C,hC,hse⟩:=hser Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hse,eventually_actual_row_data η Bcap h27,eventually_uniform_allocation_budget N Bmask,
    ColoredFrameAdmissible.eventually_actual_class_admissible 0 (19/10) εg mesh (by norm_num) hεg hmesh L θ,
    eventually_ge_atTop (2:ℝ)] with Z hs hzD hc ha hZ
  refine ⟨hZ,?_⟩
  intro C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P ξ χ₀ s rs hside hC₀ hX₁ hX₂ hcan hV₀ hCR hFhole hH hR hcap hP hQ₀ hQt hQ72
    m t Kc R radius g hg n χ v A₀ c u' err hroot hu hcol hfilled hlo hhi hmin hfees
  let labs:=FixedPhysicalClassLedger.actualFrameLabels η s θ.ha0 ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R radius rs P.j₀ ξ g n χ
  have fit:=FixedPhysicalClassLedger.actualFrameLabels_fits_caps η s θ.ha0 ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m
    t Kc R radius rs P.j₀ ξ g hg n χ hH hb hR hcap
  have good (x:GLabel θ mesh Z) (hx:x∈labs) : Supported x.G := by
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
    change Supported (g k.1)
    rcases hg k.1 with e|e
    · rw [e];exact (lab_data _ k.1).1
    · rw [e];exact (lab_data _ k.1).2.1
  have hd (x:GLabel θ mesh Z) (hx:x∈labs) : x.d=s.d := by obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx;rfl
  have hv:=FixedFrameRowWitness.sourceVolume_eq_native s rs hX₁ hX₂ hcan
  have adm:=(ha η s θ.ha0 ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R radius rs P.j₀ ξ g hg n χ
    hH hb hR hcap hlo hhi).1
  have H:=hs.2 mesh rs s η labs v (commonH rs) 0 (19/10) εg A₀ c u' err hQ₀ hQt hQ72 adm hZ hm1 hmesh.le
    hroot hu hcol hfilled hmin hv.symm fit good hd
    (fun x hx=>⟨(hc.2 θ hN hm s rs η x (fit x hx) hFhole hR hP).1,
      (hc.2 θ hN hm s rs η x (fit x hx) hFhole hR hP).2.1⟩)
    (fun x hx=>(hc.2 θ hN hm s rs η x (fit x hx) hFhole hR hP).2.2)
    (fun x hx z hrow=>hzD.2 C₀ D₀ hc₀ E₀ ξ₁ ξ₂ F P hside hC₀ ξ s θ.ha0 ω₁ ω₂ rs hX₁ hX₂ hcan
      hhi hR hV₀ hCR χ₀ Q hQ₀ m t Kc R radius g hg n χ x hx v z hrow (good x hx))
  have hpaid:=native_budget rs Q C (sourceControl S s.W₁*sourceControl S s.W₂) (fixedMarkCost s)
    _ ε u' err εg s.t₁ s.t₂ v J (Finset.univ:Finset Unit) (fun _=>u') (by simp) hC.le (fixedMarkCost_nonneg s) hfees H
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_unit,pow_one] using hpaid

#print axioms actual_class_series
end QRH.Cycle092.FixedFrameSeam
