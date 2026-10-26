/- The retained allocation cost of the pairs of a child prefix and a second-level label, by the joint count of the pairs
and the bound of one retained row. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.ProfileJointShellEnergy
import Candidate.Cycle63.Moment.DepthTwoHighRows

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

/-- The retained allocation cost of a family of pairs of a child prefix and a second-level label: the residual
allocations are contracted at each fixed encoded row, then the pairs are counted jointly over prefixes and labels by
the fixed natural dictionary, with at most `A` prefixes over each multiplier ideal. -/
theorem actual_profile_depth_two_family_energy {Index Base : Type} [Fintype Index]
    [Fintype Base] (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N) (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ {Pre : Type*} (mult : Pre → O) (left : Bool) (unit : Pre → FirstSourceLabel → O)
        (q m A a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ prefixes : Finset Pre, ∀ labels : Finset (NonzeroDepthTwoPair mult left unit),
      ∀ st : NonzeroDepthTwoPair mult left unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroDepthTwoPair mult left unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroDepthTwoPair mult left unit → Base)
        (holes : NonzeroDepthTwoPair mult left unit → Ideal O),
      (∀ l ∈ labels, l.val.1 ∈ prefixes) →
      (∀ D : Ideal O, ((prefixes.filter (fun p => Ideal.span {mult p} = D)).card : ℝ) ≤ A) →
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroDepthTwoRow l).val
          (nonzeroDepthTwoRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroDepthTwoRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.2.1.1.1 ∧ l.val.2.1.1.2 ≠ 0 ∧
        Supported l.val.2.2.1.1 ∧ l.val.2.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.2.1.1.1 = primeSupport l.val.2.1.1.2 ∧
        primeSupport l.val.2.2.1.1 = primeSupport l.val.2.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {depthTwoRow mult left unit l.val}*
        firstSourceMissing left l.val.2.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.2.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.2.1).absNorm : ℝ) ≤ Z^m) →
      ∀(F G : Finset (ℕ×ℕ)),(0,0)∈F → ∀Cprofile : ℝ,0≤Cprofile →
      ∀p : NonzeroDepthTwoPair mult left unit→Profiles ap bp,
      ∀ (S : NonzeroDepthTwoPair mult left unit → Index)
        (s : ∀ l, Data (Slots (S l))) (w σ v : ∀ l, Slots (S l) → ℝ)
        (θ : ∀ l, Slots (S l) → RayQuotient.Characters M H)
        (Ds : NonzeroDepthTwoPair mult left unit → Finset (Ideal O)),
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
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance)*A := by
  obtain ⟨J,Ccount,hCcount,hcount⟩ := actual_whole_depth_two_high_row_count M H hH
    base η₀ B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cshell,hCshell,hactual⟩ := actual_profile_high_retained_family M H hH Slots N hN P ε hε hap
  refine ⟨n,Ccount*Cshell,mul_pos hCcount hCshell,?_⟩
  filter_upwards [hactual η₀,eventually_ge_atTop (2 : ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro Pre mult left unit q m A a e allowance Kcontrol T i hq ha ha' hK hT
    prefixes labels st hQM hQη z hz index holes hpre hprefix hholes hmask hzero hsupported heq hsupport hnorm
    hmissing F G hF Cprofile hCprofile p S s w σ v θ Ds hWsrc hDs hdyad hcontrol hallowance hvalid hprofile hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hTshared : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hcard := hcount mult left unit Z hZ₂ q m A a (3*(i+1 : ℕ)*Z^P.τ)
    P.Bmask P.bΦ hq ha ha' hTshared prefixes labels st hQM hQη z hz
    (fun l => naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l)))
    index holes hpre hprefix hholes hmask hzero hsupported heq hsupport hnorm hmissing
  let W := Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpoint (l : NonzeroDepthTwoPair mult left unit) (hl : l ∈ labels) :
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
        Z^(m+q*unmarkedDensity (2*a-1)+loss)*A)*W :=
      mul_le_mul_of_nonneg_right hcard hW
    _ = _ := by
      dsimp [W]
      rw [show m+q*unmarkedDensity (2*a-1)+loss+e+allowance =
        (m+q*unmarkedDensity (2*a-1)+loss)+(e+allowance) by ring,
        Real.rpow_add hZp (m+q*unmarkedDensity (2*a-1)+loss) (e+allowance)]
      ring

end
end OAI.SevenEighths.Cycle63Moment
