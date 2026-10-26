import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.ProfileMarkedShell
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63HighResidual Cycle63HighProfiles CenteredMomentFiniteProfileExceptional
open Cycle63FinalLow CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The actual residual shell contracts before the weighted row count. All
outer geometric coefficients and varying common-volume exponents remain
inside one literal sum of natural slot weights. -/
theorem actual_profile_marked_weighted_family {Index : Type} [Fintype Index]
    (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N)
    (P : HighSourceParameters) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀a : ℝ,51/100≤a→a≤1→∀i : ℕ,
      ∀{Row : Type}(labels : Finset Row)(S : Row→ Index)
        (s : ∀l,Data (Slots (S l)))
        (st : Row→NaturalState Z P.Bmask P.bΦ)
        (hQM : ∀l,(st l).fixedModulus≤M)(hQη : ∀l,(st l).fixedModulus≤η₀.modulus)
        (z : Row→O)(hz : ∀l,(st l).radial.keep (z l))
        (w σ v : ∀l,Slots (S l)→ℝ)(θ : ∀l,Slots (S l)→RayQuotient.Characters M H),
      ∀F G : Finset (ℕ×ℕ),(0,0)∈F→∀p : Row→Profiles ap bp,
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧ (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧
        (s l).b₁=bp ∧ (s l).b₂=bp)→
      ∀Ds : Row→Finset (Ideal O),(∀l∈labels,∀L∈Ds l,Squarefree L)→
      ∀(T Cprofile Kcontrol allowance : ℝ)(e coeff : Row→ℝ),
      1≤T→0≤Cprofile→0≤Kcontrol→(∀l∈labels,0≤ coeff l)→
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T)→
      (∀l∈labels,((p l).control G)^2*(wholeControl (s l))^2≤Kcontrol)→
      (∀l∈labels,(s l).toSource.allowance Z+
        Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]≤allowance)→
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        Cycle63.Physical.sourcePositiveRow (s l).toSource b L alloc (z l)≠0→
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) hap F (p l)))→
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 0*
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 1≤Cprofile*(p l).control G)→
      (∀l∈labels,(2*a-1)*(Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume (s l))-
        ∑k,w l k)+2*P.εplain*P.d≤e l)→
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance*
        ∑l∈labels,coeff l*Z^(e l)*
          retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
            (w l) (σ l) (v l) (θ l) (s l).t := by
  obtain ⟨n,C,hC,hactual⟩:=actual_profile_marked_retained_family M H hH Slots N hN P ε hε hap
  refine ⟨n,C,hC,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Row labels S s st hQM hQη z hz w σ v θ F G hF p hWsrc Ds hDs
    T Cprofile Kcontrol allowance e coeff hT hCprofile hKcontrol hcoeff hdyad hcontrol
    hallowance hvalid hprofile hexp
  have hzpos : 0<Z:=zero_lt_one.trans hZ.1
  let K:=C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance
  have hK : 0≤K:=by dsimp [K];positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l hl => ?_
  have hr:=hZ.2 a ha ha' i (S l) (s l) (st l) (hQM l) (hQη l) (z l) (hz l)
    (w l) (σ l) (v l) (θ l) F G hF (p l) (hWsrc l hl).1 (hWsrc l hl).2.1
    (hWsrc l hl).2.2.1 (hWsrc l hl).2.2.2 (Ds l) (hDs l hl) T (e l) Cprofile hT hCprofile
    (fun L hL=>(hdyad l hl L hL).1) (fun L hL=>(hdyad l hl L hL).2)
    (hvalid l hl) (hprofile l hl) (hexp l hl)
  let wt:=retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
    (w l) (σ l) (v l) (θ l) (s l).t
  have hwt : 0≤wt:=Finset.prod_nonneg (fun _ _=>sq_nonneg _)
  have hp : Z^(e l+(s l).toSource.allowance Z+
      Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂])≤Z^(e l+allowance):=
    Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hallowance l hl])
  have hbound : (∑L∈Ds l,∑alloc∈(s l).toSource.active L,
      retainedAllocationCost (s l) L alloc (z l))≤K*Z^(e l)*wt := by
    apply hr.trans
    calc
      _=(C*Cprofile^2)*(((p l).control G)^2*(wholeControl (s l))^2)*
        (2*T)^(2*ε)*Z^(e l+(s l).toSource.allowance Z+
          Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂])*wt:=by ring
      _≤(C*Cprofile^2)*Kcontrol*(2*T)^(2*ε)*Z^(e l+allowance)*wt := by
        gcongr
        exact hcontrol l hl
      _=K*Z^(e l)*wt := by
        rw [Real.rpow_add hzpos]
        dsimp [K]
        ring
  have hh:=mul_le_mul_of_nonneg_left hbound (hcoeff l hl)
  convert hh using 1; ring

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
