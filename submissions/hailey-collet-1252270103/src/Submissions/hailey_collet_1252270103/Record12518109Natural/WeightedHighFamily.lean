/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.WeightedHighShell
import Submissions.hailey_collet_1252270103.Record12518109Natural.ResidualReserve

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators
open Cycle61Moment ResidualReserve
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61HighResidual Cycle61HighProfiles CenteredMomentFiniteProfileExceptional
open Cycle61FinalLow CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The actual residual shell contracts before the weighted row count. All
outer geometric coefficients and varying common-volume exponents remain
inside one literal sum of natural slot weights. -/
theorem actual_profile_high_weighted_family {Index : Type} [Fintype Index]
    (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N)
    (P : HighSourceParameters) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀a : ℝ,51/100≤a→a≤1→∀i : ℕ,
      ∀{Row : Type}(labels : Finset Row)(S : Row→Index)
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
      1≤T→0≤Cprofile→0≤Kcontrol→(∀l∈labels,0≤coeff l)→
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T)→
      (∀l∈labels,((p l).control G)^2*(wholeControl (s l))^2≤Kcontrol)→
      (∀l∈labels,(s l).toSource.allowance Z+
        Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]≤allowance)→
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        Cycle61.Physical.sourcePositiveRow (s l).toSource b L alloc (z l)≠0→
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) hap F (p l)))→
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 0*
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 1≤Cprofile*(p l).control G)→
      (∀l∈labels,∀k,(s l).P k=Z^(w l k))→
      (∀l∈labels,(2*a-1)*(Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume (s l))-
        ∑k,w l k)+2*P.εplain*P.d≤e l)→
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance*
        ∑l∈labels,coeff l*Z^(e l)*
          sourceSlotMaximum (s l) (z l) := by
  obtain ⟨n,C,hC,hactual⟩:=actual_profile_high_retained_weighted_family M H hH Slots N hN P ε hε hap
  refine ⟨n,C,hC,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Row labels S s st hQM hQη z hz w σ v θ F G hF p hWsrc Ds hDs
    T Cprofile Kcontrol allowance e coeff hT hCprofile hKcontrol hcoeff hdyad hcontrol
    hallowance hvalid hprofile hscale hexp
  have hzpos : 0<Z:=zero_lt_one.trans hZ.1
  let K:=C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance
  have hK : 0≤K:=by dsimp [K];positivity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hr:=hZ.2 a ha ha' i (S l) (s l) (st l) (hQM l) (hQη l) (z l) (hz l)
    (w l) (σ l) (v l) (θ l) F G hF (p l) (hWsrc l hl).1 (hWsrc l hl).2.1
    (hWsrc l hl).2.2.1 (hWsrc l hl).2.2.2 (Ds l) (hDs l hl) T (e l) Cprofile hT hCprofile
    (fun L hL=>(hdyad l hl L hL).1) (fun L hL=>(hdyad l hl L hL).2)
    (hvalid l hl) (hprofile l hl) (by
      intro L hL alloc halloc b
      let D := wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
        (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp
      have hs := high_source_exponent_frozen_saving D hZ.1 (hscale l hl) (2*a-1)
        (by linarith) (by linarith)
      have hsplit := residual_slot_width_split L alloc (w l)
      change (2*a-1)*D.total P-Cycle61.Physical.sourcePostClip (s l).toSource b Z L alloc≤
        (2*a-1)*Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume (s l))-
          (2*a-1)*(∑k∈frozenIndices L alloc,w l k) at hs
      change (2*a-1)*(D.total P-_)+2*P.εplain*P.d-_≤e l
      have hsplit' := congrArg (fun x : ℝ=>(2*a-1)*x) hsplit
      nlinarith only [hs,hsplit',hexp l hl])
  let wt:=sourceSlotMaximum (s l) (z l)
  have hwt : 0≤wt:=sourceSlotMaximum_nonneg _ _
  have hp : Z^(e l+(s l).toSource.allowance Z+
      Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂])≤Z^(e l+allowance):=
    Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hallowance l hl])
  have hbound : (∑L∈Ds l,∑alloc∈(s l).toSource.active L,
      retainedAllocationCost (s l) L alloc (z l))≤K*Z^(e l)*wt := by
    apply hr.trans
    calc
      _=(C*Cprofile^2)*(((p l).control G)^2*(wholeControl (s l))^2)*
        (2*T)^(2*ε)*Z^(e l+(s l).toSource.allowance Z+
          Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂])*wt:=by ring
      _≤(C*Cprofile^2)*Kcontrol*(2*T)^(2*ε)*Z^(e l+allowance)*wt := by
        gcongr
        exact hcontrol l hl
      _=K*Z^(e l)*wt := by
        rw [Real.rpow_add hzpos]
        dsimp [K]
        ring
  have hh:=mul_le_mul_of_nonneg_left hbound (hcoeff l hl)
  convert hh using 1 <;> ring

end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.actual_profile_high_weighted_family
