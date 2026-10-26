import Candidate.Cycle63.Moment.ProfileJointShellEnergy
import Candidate.Cycle63.Moment.ProfileShellEnergy
import Candidate.Target830.High.WholeSourceFamily
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.TargetHigh830
open Cycle63Moment CenteredMomentCanonicalFirst
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance profileJointFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_profile_joint_family_energy {Index Base : Type} [Fintype Index]
    [Fintype Base] (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N) (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
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
      C*Cprofile^2*Kcontrol*(1+3*(i+1 : ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨J,Ccount,hCcount,hcount⟩ := actual_whole_joint_high_row_count M H hH
    base η₀ B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cshell,hCshell,hactual⟩ := actual_profile_high_retained_family M H hH Slots N hN P ε hε hap
  refine ⟨n,Ccount*Cshell,mul_pos hCcount hCshell,?_⟩
  filter_upwards [hactual η₀,eventually_ge_atTop (2 : ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm
    hmissing F G hF Cprofile hCprofile p S s w σ v θ Ds hWsrc hDs hdyad hcontrol hallowance hvalid hprofile hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hTshared : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hcard := hcount left u₀ unit Z hZ₂ q m a (3*(i+1 : ℕ)*Z^P.τ)
    P.Bmask P.bΦ hq ha ha' hTshared labels st hQM hQη z hz
    (fun l => naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l)))
    index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
  let W := Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0 ≤ W := by dsimp [W]; positivity
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
    _ = (labels.card : ℝ)*W := by simp [nsmul_eq_mul]
    _ ≤ (Ccount*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
        Z^(m+q*unmarkedDensity (2*a-1)+loss))*W :=
      mul_le_mul_of_nonneg_right hcard hW
    _ = _ := by
      dsimp [W]
      rw [show m+q*unmarkedDensity (2*a-1)+loss+e+allowance =
        (m+q*unmarkedDensity (2*a-1)+loss)+(e+allowance) by ring,
        Real.rpow_add hZp (m+q*unmarkedDensity (2*a-1)+loss) (e+allowance)]
      ring

/-- Residual allocations are contracted at each fixed encoded row; only
then is the joint physical pool counted by the fixed natural dictionary. -/

theorem actual_profile_joint_shell_energy {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
      ∀(F G : Finset (ℕ×ℕ)),(0,0)∈F → ∀Cprofile : ℝ,0≤Cprofile →
      ∀p : NonzeroJointSourceLabel left u₀ unit→Profiles ap bp,
      ∀ (S : NonzeroJointSourceLabel left u₀ unit → Finset α)
        (s : ∀ l, Data (S l)) (w σ v : ∀ l, S l → ℝ)
        (θ : ∀ l, S l → RayQuotient.Characters M H)
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
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle63.Physical.sourcePostClip (s l).toSource b Z L alloc ≤ e) →
      (∑ l ∈ labels, ∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1 : ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  exact actual_profile_joint_family_energy M H hH (fun S : Finset α=>↥S)
    (Fintype.card α) (fun S=>by simpa using Finset.card_le_univ S)
    base η₀ B Q loss ε hB hQ hQB hloss hε hap

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_profile_joint_family_energy
#print axioms OAI.SevenEighths.TargetHigh830.actual_profile_joint_shell_energy
