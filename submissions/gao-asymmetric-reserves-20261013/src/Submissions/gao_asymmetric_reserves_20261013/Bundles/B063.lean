/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B002
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B030
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B039
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B045
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B048
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B049
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B051
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B057
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B060
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B061
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeChoice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowGlobalBudget

/- BEGIN ORIGINAL MODULE Cycle25.Energy.NaturalHighStage ; sha256 b99fd81043059084488a87db5ea146cc4c1f44748c43c0f96f74bcc4e6480d28 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/NaturalHighStage.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyNaturalHighStage
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open Cycle25CenteredMomentEnergyPositiveHighSource Cycle25CenteredMomentEnergyPositiveHighSourceBound
open Cycle25CenteredMomentEnergyPositiveHighParameters Cycle25CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins Cycle25CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_high_stage
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hrho:0< rho)(hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(7/10:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(lowDegree:ℕ)(Slow:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→0≤ Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      CenteredMomentEnergyReferenceLowBands.PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask
        (Mparent+Bmask+rho/100) Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z η₀ Q
        lowDegree Slow Clow→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi rho Mparent
        (reflectedLoss Mglobal B ε k) κ Z η₀ Q J U (C*(C₀+C₁+Clow+1)) := by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hb:0≤ b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hr4:0< r/4:=by positivity
  have hs:0< amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
  obtain ⟨Ψ,hΨs,hΨn,hstage⟩:=actual_high_stage_from_physical (α:=α) M H hH
    W hW.continuous aslot bslot lo hi a b bΦ rho r Mparent Bmask (r/4) (r/4)
    (2*amplification ε+1) haslot hWs hbslot ha hlo hhi hbΦ hrho hr hMp hBm hr4 hr4
  obtain ⟨Up,Jp,hphysical⟩:=Cycle25CenteredMomentEnergyPositiveHighPhysical.actual_positive_high_physical
    (α:=α) M H hH W hW aslot bslot lo hi a b bΦ haslot hWs hbslot ha hb
    Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε k hMg hA hB hBm hMp hMc hL hLs
    hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  obtain ⟨J,U,Cf,hCf,hstageZ⟩:=hstage lowDegree Slow Jp Up
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphysZ⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cf*(Cp+1),by positivity,?_⟩
  filter_upwards [hstageZ,hphysZ] with Z hstageNow hphysicalNow
  refine ⟨hphysicalNow.1,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hzero hpos hlow
  have hp:=hphysicalNow.2 εchild C₀ C₁ hchild hC₀ hC₁ hzero hpos
  have hm:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hmass:0≤ Cp*(C₀+C₁+1):=by positivity
  have hh:=hstageNow.2 Lgoal Lslot κ (physicalLoss Mglobal B ε k)
    (physicalLoss Mglobal B ε k) (reflectedLoss Mglobal B ε k) η₀ Q
    Clow (Cp*(C₀+C₁+1)) hκ hm.1.le hClow hmass
    (by exact le_rfl) hm.2.2.2.1 (hm.2.2.1.trans hm.2.2.2.1)
    (by have hpos:=hm.1.le.trans hm.2.2.2.1;linarith only [hpos,hs]) hlow hp
  have hconst:Cf*(Clow+Cp*(C₀+C₁+1)+1)≤(Cf*(Cp+1))*(C₀+C₁+Clow+1):=by
    have hh:0≤ Cp*Clow:=mul_nonneg hCp.le hClow
    nlinarith only [mul_nonneg hCf.le hh,mul_nonneg hCf.le hC₀,mul_nonneg hCf.le hC₁]
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge
  apply (hh T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge).trans
  have hd:=diagonalControl_nonneg state.radial.profile
  have hp0:=p.control_nonneg U
  have hz:0≤ Z:=zero_le_one.trans hphysicalNow.1.le
  gcongr

end SevenEighths.Cycle25CenteredMomentEnergyNaturalHighStage

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.NaturalHighStage -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.PacketBinBound ; sha256 854dfc532a596a71214981a9b8093738b6a838240aafb1f0a0e68c8549e3b2f4 -/
section


/-! The complete coefficient-packet and dilation-bin estimate. All infinite
coefficient sums and rowwise choice moments have been eliminated here. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_weighted_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (kap U xi : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L z delta loss epsilon Ccount Cmoment M : ℝ)
    (hkap : 7/10 ≤ kap) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι : ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i * N i e) ≤ U^((n : ℝ)*xi))
    (hseries : ∀ i, Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/4)))
    (hmass : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/4)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*selectedCapacity kap z ((j : ℝ)*xi+xi)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/4 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/4) M
    (fun e=> max 1 (Lc i*N i e)) (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/4) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/4) M hU0 hM.ne'
      (fun e=> max 1 (Lc i*N i e)) (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 3
    ring
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/4) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_weighted_dilation_bins Finset.univ n B Q P _ kap U R q L z xi delta loss epsilon
    Ccount Cmoment M hkap hU hc hm hM.le hq hqdelta hxi (by simpa using hcard)
    (fun i hi=> hsplit i) (fun j hj i hi=> hselected j hj i) (fun i hi=> hfull i) henergy

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.PacketBinBound -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowGlobalBudget ; sha256 b571a9cfac4525e64deaf87e91c32109667e99c485bbc83a8caf04fb44b12da5 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowGlobalBudget.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤ Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤ Z^Lrow → (QP/2)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤ Z^Lcap → QK≤ Z^Lcap → QP≤ Z^Lcap → -saving≤((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  let q := (Fintype.card (Eis⧸Ideal.span {Nlevel^2}):ℝ)
  have hq : 0≤ q := Nat.cast_nonneg _
  refine ⟨degree,q^3*C+1,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0< Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      exact henergy J I F Q Q₀ hJ hI hQ hpower hmask A
        Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
        hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
        hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
        hFcap hscap hpool (fullRaySector Nlevel rows r₀) (fullRaySector Nlevel Pset p₀) S
        (fun K hK => hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
        (fun K hK => hrowcop K (Finset.mem_filter.mp hK).1)
        (fun P hP => hprod P (Finset.mem_filter.mp hP).1)
        (fun P hP => hScop P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSN P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSchar P (Finset.mem_filter.mp hP).1)
        θ r aw hqk hqp
        (fun K hK => hKr K (Finset.mem_filter.mp hK).1)
        (fun P hP => hPr P (Finset.mem_filter.mp hP).1)
        (fun K hK => hr K (Finset.mem_filter.mp hK).1)
        (fun P hP => haw P (Finset.mem_filter.mp hP).1))
  apply hs.trans
  change q^3*(C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2))≤_
  have hp : 0≤(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowGlobalBudget -/

/- BEGIN ORIGINAL MODULE Global.Transport.CanonicalCubeChoice ; sha256 a4d8a9bdb1f41781365674a3962297ba258a47086947f9833e23aadd912cbf59 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_exists_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∃n : ℕ,0 < n ∧ ∀(η : Character) (Z : ℝ),1≤ Z → 2 < Z^τ →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀ψ : FreeRow→ι→Character,∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (ψ u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (ψ u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) T hT W (fun i=> Z^(length i))
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_probe_minus_cube (ι:=ι) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha hb hB hβ S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  intro η Z hZ hZT T hT hdis length hl0 hl hpool W hWS hWB ψ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he hZT n hn hwidth S hS.prime η ψ
  refine ⟨idx,grid,?_,?_,?_⟩
  · intro u
    exact ⟨(hbins u).1,(hbins u).2.1,(hbins u).2.2.1,(hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    exact ⟨ha0,ha1,hlo,hhi,hnext,hzero⟩
  · apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
      (fun u=>51/100+e*grid u) (fun _=> Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx ψ
    intro u hu
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    refine ⟨ha0,ha1,hZT,hBH,?_,hnext⟩
    have : 0≤ Z^τ := Real.rpow_nonneg (by linarith) _
    linarith

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CanonicalCubeChoice -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderNormalized ; sha256 8c421500fc950e21d713bf60eb5381d1a89bd02ffe9bf9135d00361a9fdc7467 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/





noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace Submission20261012.Global.Transport.PrincipalNormalized
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
open Submission20261012.Global.Transport.PrincipalResidueActual Submission20261012.Global.Transport.PrincipalRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0 ≤ c) (hA : ‖A-R‖ ≤ c) (hN : ‖N⁻¹‖ ≤ v)
    (hR : ‖R/N-F‖ ≤ d) : ‖A/N-F‖ ≤ c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _  ≤  ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _  ≤  c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B) (hmin : 0< ellMin)
    (slotEll : Fin K→ℝ) (hell : ∀j,ellMin ≤ slotEll j) (hdis : Function.Injective slotEll)
    (hsum : (∑j,slotEll j)=ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0 ≤ (W0 y).re) (hp1 : ∀y,0 ≤ (W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0< e) (hehi : e ≤ 1/1000) (hnu : 0< nu)
    (ha : theta < HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e ≤ 2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(slotEll j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z ell
          (slotMass T (residueWeights W (fun j=> Z^(slotEll j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotEll j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryGenerator (P j).val.val)
          W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (PrincipalSignal.signalShift) Z‖ ≤
      C*(Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000+nu)+
        Z^(HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := Submission20261012.Global.Transport.PrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := Submission20261012.Global.Transport.PrincipalResidueActual.normalized_actual_window_residue S hS η ha ha2 (by linarith [Submission20261012.Global.Transport.theta_bounds]) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(theta :ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [Submission20261012.Global.Transport.PrincipalRaySlots.power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin slotEll hell,
    OAI.SevenEighths.ProbeRaySlots.power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne slotEll (fun j=> hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=> c) (fun _=> d) slotEll (fun _=> hc) (fun _=> hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0< Z := by linarith [Submission20261012.Global.Transport.theta_bounds]
  let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(slotEll j))
  let normer := cs*(Probe.principalScalar Finset.univ Z ell
    (slotMass T (residueWeights W (fun j=> Z^(slotEll j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=> Z^(slotEll j)) (c*Z^ellMin) (Z^(ly:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=> hmass.1 j) hZ
  dsimp only at hr ⊢
  simp only [PrincipalSignal.signalShift, neg_div, ← sub_eq_add_neg] at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem slotEll hsum W hWbounds (fun j=> Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖ ≤ ‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(theta :ℝ))=c^(-(theta :ℝ))*Z^(-(theta :ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-(4+b)/6)*(c*Z^ellMin)^(-(theta :ℝ))=
      (D*c^(-(theta :ℝ)))*Z^(HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin=
      (HeckeZeroSupremum.beta+e-(4+b)/6)+(-(theta :ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖ ≤ C := by
    dsimp [C]
    have : 0 ≤ D*c^(-(theta :ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(theta :ℝ)) ≤ C := by
    dsimp [C]
    have : 0 ≤ C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _  ≤  C*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000+nu)+
        C*Z^(HeckeZeroSupremum.beta-(4+b)/6+e-(theta )*ellMin) := by gcongr
    _ = _ := by ring
end Submission20261012.Global.Transport.PrincipalNormalized
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderNormalized -/

/- BEGIN ORIGINAL MODULE Physical.Mass ; sha256 5e1ea56527a1b179d6186707c9e5db330a73e12fa7740092bfad9378530c0208 -/
section

noncomputable section
open scoped Classical BigOperators
namespace Local44.Physical
open Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily
open ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem half_mass_contour_gates {a e first : ℝ}
    (ha : (51 / 100 : ℝ) ≤ a) (hatop : a ≤ 7 / 8)
    (he : 0 < e) (hfirst : first ≤ 16 * e) :
    0 ≤ (2 * a - 1) / 2 ∧ (2 * a - 1) / 2 ≤ 1 ∧
    1 - a - 6 * e ≤ 1 / 2 - (2 * a - 1) / 2 ∧
    -(1 / 100 : ℝ) ≤ 1 / 2 - (2 * a - 1) / 2 ∧
    1 + first ≤ a + 16 * e + (1 / 2 - (2 * a - 1) / 2) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_physical_half_mass (epsilon c d B : ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (W : ι → ℝ → ℂ) (Y : ι → ℝ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ (x z : ℂ) (alpha eps Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 7 / 8 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → firsteps ≤ 16 * eps →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^((2*alpha-1)/2)) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^((2*alpha-1)/2)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon * ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  obtain ⟨C, hC, hmass⟩ := actual_physical_label_mass (ι:=ι) epsilon c d B hepsilon hc hd hB
  refine ⟨C, hC, ?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη W Y hY hWS hWB x z alpha eps Ccond Cu
    ha hatop he he1 hx hz hfirsteps hCcond hCu0 hCu
  obtain ⟨hrho, hrho1, hline, hleft, hmargin⟩ := half_mass_contour_gates ha hatop he hfirsteps
  exact hmass S hS firsteps hfirst η u T hT hdis hη W Y hY hWS hWB x z
    alpha eps ((2*alpha-1)/2) Ccond Cu ha (by linarith) he he1 hx hz
    hrho hrho1 hline hleft (by simpa only [hx] using hmargin) hCcond hCu0 hCu

end Local44.Physical
end
/- END ORIGINAL MODULE Physical.Mass -/
