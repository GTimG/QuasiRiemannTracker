/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Arvi (2026-10-25): the contrary hypothesis `theta < beta` is replaced by
`51/100 ≤ beta`, the only consequence of it that the source construction uses.
Specializes the full-ball estimate to the actual source root using an
explicit raw-side estimate. The caps and the low/high minimum are supplied
by the literal source setup.
Modified by Sil (2026-10-26): indexed by G and ProviderAt G eps meshCap; roots are Setup M H D with slot widths <= min (mesh G eps) meshCap and the lower end hs0 : s0 <= markedWidth as explicit inputs (roots below s0 are inherited by the assembly); output Z^(1+4 eps); NeedsCentering/rootReference/centeredRoot of G; product cap via marked_width_cap.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceBallSupply

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceActualBall
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedFirstProfileEnvelope
open RestoredRootDictionary RestoredRootEnergy
open Qrh.MarkedAnchor.Ordinary.RootParameters RepairedRawContext RepairedSourceSideSupply RepairedSourceProfiles
open RepairedSourceRootGeometry RepairedSourceRootInput RepairedSourceBallSupply
open RecenteredRootSetup RecenteredRootReferenceCaps RecenteredRootFixedMajorant
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqActualBall {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance instFiniteQuotActualBall (M : Id) [NeZero M] : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

set_option maxHeartbeats 1500000 in
theorem uniform_actual_ball_of_side_provider {D : StepData} (G : StepGates D)
    (ε : ℝ) (hε : 0 < ε) (meshCap : ℝ) (hsupply : ProviderAt G ε meshCap) (α : Type) [Fintype α]
    (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q : Id) [NeZero Q]
    (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H D T0,
      s.Z=Z → s.W=W → s.η₀=η₀ → s.Lcap=windowCap G (Fintype.card α) ε →
    ∀ V : ℝ, 0 ≤ V → (∀i,|s.v i| ≤ V) → (∀i,s.w i ≤ min (mesh G ε) meshCap) → ∀ hs₀ : D.s₀ ≤ markedWidth M H s,
    ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
      ((¬NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s)) →
        fullBallCost (s.rootSource hH hn₁ hn₂) (by norm_num) η (bΦ*Z) ≤
          C*(s.p.control control)^2*(1+|s.t|+V)^J*Z^(1+4*ε)) ∧
      (∀ hhigh : NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s),
        ∀ h₁ : rootReference M H G s ε ≤ s.Y₁, ∀ h₂ : rootReference M H G s ε ≤ s.Y₂,
        fullBallCost (centeredRoot M H hH G s ε hε hn₁ hn₂ hs₀ hhigh h₁ h₂) (by norm_num) η (bΦ*Z) ≤
          C*(s.p.control control)^2*(1+|s.t|+V)^J*Z^(1+4*ε)) := by
  obtain ⟨J,control,C,hC,hball⟩ := uniform_ball_of_side_provider G ε hε meshCap hsupply α M H hH
    W hW hWs bΦ hbΦ η η₀ Q hQt hQ72 hQM hQη
  refine ⟨J,control,C*3^J,mul_pos hC (by positivity),?_⟩
  filter_upwards [hball,eventual_root_caps (α:=α) M H hH (Fintype.card α) ε bΦ hε hbΦ η]
    with Z hb hc
  refine ⟨hc.1,?_⟩
  intro T0 s hsZ hsW hsη hLc V hV hfreq hwm' hs₀ hn₁ hn₂
  have hwm : ∀ i, s.w i ≤ mesh G ε := fun i => (hwm' i).trans (min_le_left _ _)
  have hcap : ∀ i : remainingSet s.r s.A, s.w i.val ≤ meshCap := fun i => (hwm' i.val).trans (min_le_right _ _)
  subst Z
  cases hsW
  cases hsη
  have hcaps := hc.2.2.2.2 T0 s rfl hn₁ hn₂
  have hP : (∏i,(s.rootSource hH hn₁ hn₂).P i) ≤ s.Z^(8:ℝ) := by
    rw [root_product M H hH s hn₁ hn₂]
    exact Real.rpow_le_rpow_of_exponent_le s.hZ.le (by linarith [marked_width_cap M H s, s.hD.2.2])
  have hzpow : 0 ≤ s.Z^(1+4*ε) := Real.rpow_nonneg (zero_lt_one.trans s.hZ).le _
  constructor
  · intro hlow
    let d := lowInput M H hH G ε hε T0 s hLc V bΦ hV hbΦ hfreq hwm hs₀ η
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hn₁ hn₂ hcaps.1 hlow
    have he := hb.2 (⟨T0,remainingSet s.r s.A⟩ : RootShape α) d rfl hcap hP hcaps.2.1 hcaps.2.2
    have ha := actual_amplitude_bound d.root s.p rfl rfl s.t V hV rfl rfl J control C hC.le
    have hh := mul_le_mul_of_nonneg_right ha hzpow
    have ht0 : d.t₀ = s.t := rfl
    have hheight : d.V = V := rfl
    exact he.trans (by simpa only [amplitude, ht0, hheight] using hh)
  · intro hhigh h₁ h₂
    let d := highInput M H hH G ε hε T0 s hLc V bΦ hV hbΦ hfreq hwm hs₀ η
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hn₁ hn₂ hcaps.1 hhigh h₁ h₂
    have he := hb.2 (⟨T0,remainingSet s.r s.A⟩ : RootShape α) d rfl hcap hP hcaps.2.1 hcaps.2.2
    have ha := actual_amplitude_bound d.root s.p rfl rfl s.t V hV rfl rfl J control C hC.le
    have hh := mul_le_mul_of_nonneg_right ha hzpow
    have ht0 : d.t₀ = s.t := rfl
    have hheight : d.V = V := rfl
    exact he.trans (by simpa only [amplitude, ht0, hheight] using hh)

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceActualBall
