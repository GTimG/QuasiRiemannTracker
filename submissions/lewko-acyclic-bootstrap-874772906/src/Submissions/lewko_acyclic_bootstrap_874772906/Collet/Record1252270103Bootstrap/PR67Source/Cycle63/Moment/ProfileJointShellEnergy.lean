import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ProfileShellEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceDatum
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighResidualAllocation
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Residual allocations are contracted at each fixed encoded row, and the labels are summed pointwise: the energy is
at most the pointwise bound times the number of labels. The labels are counted by the caller. -/
theorem actual_profile_joint_family_energy {Index : Type} [Fintype Index]
    (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N) (η₀ : Character)
    (ε : ℝ) (hε : 0 < ε) {ap bp : ℝ} (hap : 0<ap) :
    ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (a e allowance Kcontrol T : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l)),
      ∀(F G : Finset (ℕ×ℕ)),(0,0)∈F → ∀Cprofile : ℝ,0≤Cprofile →
      ∀p : NonzeroJointSourceLabel left u₀ unit→Profiles ap bp,
      ∀ (S : NonzeroJointSourceLabel left u₀ unit → Index)
        (s : ∀ l, Data (Slots (S l))) (w σ v : ∀ l, Slots (S l) → ℝ)
        (θ : ∀ l, Slots (S l) → RayQuotient.Characters M H)
        (Ds : NonzeroJointSourceLabel left u₀ unit → Finset (Ideal O)),
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, Squarefree L) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, T ≤ (L.absNorm : ℝ) ∧ (L.absNorm : ℝ) < 2*T) →
      (∀ l ∈ labels, ((p l).control G)^2*(wholeControl (s l))^2 ≤ Kcontrol) →
      (∀ l ∈ labels, (s l).toSource.allowance Z+
        Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂] ≤ allowance) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        Cycle63.Physical.sourcePositiveRow (s l).toSource b L alloc (z l)≠0 →
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) hap F (p l))) →
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 0*
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 1≤Cprofile*(p l).control G) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
          (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*N-
          Cycle63.Physical.sourcePostClip (s l).toSource b Z L alloc ≤ e) →
      (∑ l ∈ labels, ∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)*labels.card := by
  intro P
  obtain ⟨n,Cshell,hCshell,hactual⟩ := actual_profile_high_retained_family M H hH Slots N hN P ε hε hap
  refine ⟨n,Cshell,hCshell,?_⟩
  filter_upwards [hactual η₀,eventually_ge_atTop (2 : ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit a e allowance Kcontrol T i ha ha' hK hT
    labels st hQM hQη z hz F G hF Cprofile hCprofile p S s w σ v θ Ds hWsrc hDs hdyad hcontrol hallowance hvalid
    hprofile hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  let W := Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)
  have hpoint (l : NonzeroJointSourceLabel left u₀ unit) (hl : l ∈ labels) :
      (∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤ W := by
    have hr := hZ.2 a (by linarith : 51/100 ≤ a) (by linarith : a ≤ 1) i (S l) (s l)
      (st l) (hQM l) (hQη l) (z l) (hz l) (w l) (σ l) (v l) (θ l)
      F G hF (p l) (hWsrc l hl).1 (hWsrc l hl).2.1 (hWsrc l hl).2.2.1 (hWsrc l hl).2.2.2
      (Ds l) (hDs l hl) T e Cprofile hT hCprofile (fun L hL => (hdyad l hl L hL).1)
      (fun L hL => (hdyad l hl L hL).2) (hvalid l hl) (hprofile l hl) (hexp l hl)
    apply hr.trans
    dsimp [W]
    have he := Real.rpow_le_rpow_of_exponent_le hZ.1.le
      (show e+(s l).toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]
        ≤e+allowance by linarith [hallowance l hl])
    calc
      _ = (Cshell*Cprofile^2)*(((p l).control G)^2*(wholeControl (s l))^2)*(2*T)^(2*ε)*
          Z^(e+(s l).toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]) := by ring
      _ ≤ (Cshell*Cprofile^2)*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcontrol l hl) (by positivity))
            (Real.rpow_nonneg (by positivity) _)
        · exact he
        · positivity
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ _l ∈ labels, W := Finset.sum_le_sum hpoint
    _ = W*(labels.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = _ := by dsimp [W]

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
