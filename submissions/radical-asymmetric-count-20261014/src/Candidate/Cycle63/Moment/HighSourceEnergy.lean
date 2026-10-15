import Candidate.Cycle63.Moment.HighSourceRows
import Candidate.Cycle63.Moment.PhysicalHighRows

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros LocalMoment
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open LowBranch CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

structure HighSourceParameters where
  Wslot : ℝ → ℂ
  (A₀ B₀ : ℝ)
  hA₀ : 0 < A₀
  hWs : Function.support Wslot ⊆ Icc A₀ B₀
  hW : ContDiff ℝ ∞ Wslot
  (Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax : ℝ)
  (bΦ Mcap Bmask margin d : ℝ)
  hRw : 0 ≤ Rwidth
  hRp : 0 ≤ Rplain
  hdmax : 0 ≤ dmax
  hτ : 0 < τ
  hεs : 0 < εslot
  hεp : 0 < εplain
  he : 0 < e
  he' : e < 1/1000
  hκ : 0 < κ
  hκ' : κ ≤ 1
  hvp : 0 ≤ vplain
  hvs : 0 ≤ vslot
  hslotBudget : 8*e*Rwidth+κ ≤ εslot
  hplainBudget : 12*e*(Rplain+2)+8*κ+2*vplain ≤ εplain
  hbΦ : 0 ≤ bΦ
  hmargin : 0 < margin
  hd : 0 < d
  hdsupply : Mcap+Bmask+margin ≤ d
  hdm : d ≤ dmax
  profileBound : ℕ → ℝ
  hprofile : ∀ k, 0 ≤ profileBound k

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A dependent index retains the literal live slot type of each source.
Its analytic requirements below are structural, buffered-zero and profile gates. -/
structure HighSourceDatum (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (Dict : Type*) [Fintype Dict] where
  state : NaturalState Z P.Bmask P.bΦ
  hQM : state.fixedModulus ≤ M
  hQη : state.fixedModulus ≤ η₀.modulus
  z : O
  hz : state.radial.keep z
  natural : NaturalRow state.character z
  character : Dict → Character
  hcharacter : ∀ j, (character j).residue ≠ 1
  member : Dict
  Slot : Type
  [slotFintype : Fintype Slot]
  [slotDecidableEq : DecidableEq Slot]
  source : Data Slot
  second : Bool
  projector : Ideal O
  allocation : Allocation projector (Finset.univ : Finset (Slot ⊕ Fin 2))
  (w σ v : Slot → ℝ)
  θ : Slot → RayQuotient.Characters M H
  t : ℝ
  W : Fin 2 → ℝ → ℂ
  (X r A B : Fin 2 → ℝ)

attribute [instance] HighSourceDatum.slotFintype HighSourceDatum.slotDecidableEq

variable {M H}
variable {Dict : Type*} [Fintype Dict]

def HighSourceDatum.total (P : HighSourceParameters) {η₀ : Character} {Z : ℝ}
    (D : HighSourceDatum M H P η₀ Z Dict) : ℝ :=
  (∑ j, Real.logb Z (clippedScale
    (Cycle63.Physical.sourcePlainScales D.source.toSource D.second j)))+
    (∑ k, D.w k)-Cycle63.Physical.clippedReduction
      (Real.logb Z (formalReductionFactor D.projector D.allocation D.source.P))
      (fun j => Real.logb Z (Cycle63.Physical.sourcePlainScales D.source.toSource D.second j))
      (Cycle63.Physical.actualPlainReduction Z D.projector D.allocation)

def HighSourceDatum.liveCard (P : HighSourceParameters) {η₀ : Character} {Z : ℝ}
    (D : HighSourceDatum M H P η₀ Z Dict) : ℕ :=
  (liveIndices D.projector D.allocation).card

def HighSourceDatum.row (P : HighSourceParameters) {η₀ : Character} {Z : ℝ}
    (D : HighSourceDatum M H P η₀ Z Dict) : ℂ :=
  Cycle63.Physical.sourcePositiveRow D.source.toSource D.second D.projector D.allocation D.z

structure HighSourceAdmissible (P : HighSourceParameters) (η₀ : Character) (Z a : ℝ)
    (i n : ℕ) (D : HighSourceDatum M H P η₀ Z Dict) : Prop where
  width : D.state.width ≤ P.Mcap
  low : ActualLow M H hH D.state η₀ D.hQM D.hQη a P.e
    (3*(i+1 : ℕ)*Z^P.τ) D.z
  member : D.character D.member = excluded D.natural.character D.state.puncture
  upper : zeroMaximum D.character D.hcharacter (3*(i+1 : ℕ)*Z^P.τ) < a+2*P.e
  modulus : (D.character D.member).modulus.absNorm ≤ Z^P.d
  character : D.source.η = D.state.character
  mask : D.source.m = D.state.mask
  A : D.source.A = 1
  height : D.source.t = D.t
  pool : ∀ k, D.source.slots k = primePool M H P.B₀ (Z^(D.w k))
  coefficient : ∀ k I, D.source.coefficient k I =
    idealCoeff (relativeCharacter M H hH η₀ (D.θ k)) I*
      annularWeight P.Wslot (Z^(D.w k)) (D.σ k) (D.v k) I
  scale : ∀ k, D.source.P k = Z^(D.w k)
  w_nonneg : ∀ k, 0 ≤ D.w k
  w_bound : ∀ k, D.w k/P.d ≤ P.Rwidth
  σ_lower : ∀ k, P.σmin ≤ D.σ k
  σ_upper : ∀ k, D.σ k ≤ P.σmax
  slot_frequency : ∀ k, |D.t+D.v k|+Z^P.τ/2 ≤ (3*i+2 : ℕ)*Z^P.τ
  slot_height : (3+(3*i+2 : ℕ)*Z^P.τ)^2 ≤ (Z^P.d)^P.vslot
  plain_frequency : |D.t|+Z^P.τ/2 ≤ (3*i+2 : ℕ)*Z^P.τ
  plain_height : (3+(3*i+2 : ℕ)*Z^P.τ)^4 ≤ (Z^P.d)^P.vplain
  W₁ : D.source.W₁ = D.W 0
  W₂ : D.source.W₂ = D.W 1
  post_scale : ∀ k, Cycle63.Physical.postPlainScale D.projector D.allocation
    (Cycle63.Physical.sourcePlainScales D.source.toSource D.second) k = D.X k
  X_pos : ∀ k, 0 < D.X k
  clipped_scale : ∀ k, clippedScale (D.X k) = (Z^P.d)^(D.r k)
  A_pos : ∀ k, 0 < D.A k
  support : ∀ k, Function.support (dilated (D.W k) (clipDilation (D.X k))) ⊆ Icc (D.A k) (D.B k)
  smooth : ∀ k, ContDiff ℝ ∞ (dilated (D.W k) (clipDilation (D.X k)))
  r_nonneg : ∀ k, 0 ≤ D.r k
  r_bound : ∀ k, D.r k ≤ P.Rplain
  mellin₂ : ∀ k, ∀ x ∈ Icc (1-a-6*P.e) 2, ∀ u : ℝ,
    (1+|u|)^2*‖mellin (dilated (D.W k) (clipDilation (D.X k)))
      ((x : ℂ)+u*Complex.I)‖ ≤ P.profileBound 2
  mellin_n : ∀ k, ∀ x ∈ Icc (1-a-6*P.e) 2, ∀ u : ℝ,
    (1+|u|)^(n+2)*‖mellin (dilated (D.W k) (clipDilation (D.X k)))
      ((x : ℂ)+u*Complex.I)‖ ≤ P.profileBound (n+2)

variable (M H)

theorem actual_high_source_datum (P : HighSourceParameters) :
    ∃ n : ℕ, ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧
      ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 → ∀ i : ℕ,
      ∀ {Dict : Type*} [Fintype Dict] (D : HighSourceDatum M H P η₀ Z Dict),
      HighSourceAdmissible hH P η₀ Z a i n D →
        ‖D.row P‖^2 ≤ Cp^2*Cs^(D.liveCard P)*
          Z^((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(D.liveCard P)) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hrow⟩ := actual_high_source_row M H hH
    P.Wslot P.A₀ P.B₀ P.hA₀ P.hWs P.hW
    P.Rwidth P.Rplain P.dmax P.τ P.εslot P.εplain P.e P.κ P.vplain P.vslot
    P.σmin P.σmax P.bΦ P.Mcap P.Bmask P.margin P.d
    P.hRw P.hRp P.hdmax P.hτ P.hεs P.hεp P.he P.he' P.hκ P.hκ' P.hvp P.hvs
    P.hslotBudget P.hplainBudget P.hbΦ P.hmargin P.hd P.hdsupply P.hdm
    P.profileBound P.hprofile
  refine ⟨n,Cp,Cs,hCp,hCs,?_⟩
  intro η₀
  filter_upwards [hrow η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Dict _ D hD
  exact hZ.2 D.state hD.width D.hQM D.hQη a i ha ha' D.z D.hz D.natural hD.low
    D.character D.hcharacter D.member hD.member hD.upper hD.modulus
    D.w D.σ D.v D.θ D.t D.source D.second D.projector D.allocation
    hD.character hD.mask hD.A hD.height hD.pool hD.coefficient hD.scale hD.w_nonneg
    hD.w_bound hD.σ_lower hD.σ_upper hD.slot_frequency hD.slot_height
    hD.plain_frequency hD.plain_height D.W D.X D.r D.A D.B hD.W₁ hD.W₂
    hD.post_scale hD.X_pos hD.clipped_scale hD.A_pos hD.support hD.smooth
    hD.r_nonneg hD.r_bound hD.mellin₂ hD.mellin_n

theorem high_source_datum_cap (P : HighSourceParameters) {η₀ : Character} {Z a : ℝ}
    {D : HighSourceDatum M H P η₀ Z Dict} {Cp Cs E : ℝ} {N : ℕ}
    (hZ : 1 ≤ Z) (hCs : 0 ≤ Cs) (ha : 1/2 ≤ a)
    (hrow : ‖D.row P‖^2 ≤ Cp^2*Cs^(D.liveCard P)*
      Z^((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(D.liveCard P)))
    (hwidth : D.total P ≤ E) (hcard : D.liveCard P ≤ N) :
    ‖D.row P‖^2 ≤ Cp^2*(max 1 Cs)^N*
      Z^((2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  have hCp : 0 ≤ Cp^2 := sq_nonneg Cp
  have hpow : Cs^(D.liveCard P) ≤ (max 1 Cs)^N :=
    (pow_le_pow_left₀ hCs (le_max_right 1 Cs) _).trans
      (pow_le_pow_right₀ (le_max_left 1 Cs) hcard)
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hcardR : (D.liveCard P : ℝ) ≤ N := by exact_mod_cast hcard
  have hε : 0 ≤ 2*P.εslot*P.d :=
    mul_nonneg (mul_nonneg (by norm_num) P.hεs.le) P.hd.le
  have hexp : (2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(D.liveCard P) ≤
      (2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N := by
    nlinarith [mul_le_mul_of_nonneg_left hwidth hδ,
      mul_le_mul_of_nonneg_left hcardR hε]
  exact hrow.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hCp)
    (Real.rpow_le_rpow_of_exponent_le hZ hexp) (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    (mul_nonneg hCp (pow_nonneg (le_trans zero_le_one (le_max_left 1 Cs)) _)))

/-- The density degree is chosen before the analytic parameters, hence before
τ. Source norms are supplied by actual buffered plain/slot estimates, while
all row multiplicities come from the fixed natural dictionary. -/
theorem actual_joint_high_source_energy {Base Family : Type*} [Fintype Base] [Fintype Family]
    (base : Base → Character) (B Q loss : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a E : ℝ) (i : ℕ), q ≤ Q → 33/40 ≤ a → a ≤ 7/8 →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ D : NonzeroJointSourceLabel left u₀ unit → HighSourceDatum M H P η₀ Z Family,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Base,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      (∀ l ∈ labels, HighSourceAdmissible hH P η₀ Z a i n (D l)) →
      (∀ l ∈ labels, (D l).total P ≤ E ∧ (D l).liveCard P ≤ N) →
      (∀ l ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff ((D l).character j) I =
        idealCoeff (excluded (naturalRow (base (dictionary l j))
          (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (puncture l j)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ zeroMaximum (D l).character (D l).hcharacter (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^m) →
      (∑ l ∈ labels, ‖(D l).row P‖^2) ≤
        C*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
          Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
            2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  obtain ⟨J,Cd,hCd,hcount⟩ := actual_joint_buffered_high_row_count base B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cp,Cs,hCp,hCs,hrow⟩ := actual_high_source_datum M H hH P
  let K := Cp^2*(max 1 Cs)^N
  have hK : 0 < K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left 1 Cs)) _)
  refine ⟨n,Cd*K,mul_pos hCd hK,?_⟩
  intro η₀
  filter_upwards [hrow η₀, eventually_ge_atTop (2:ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit q m a E i hq ha ha' labels D dictionary puncture
    hvalid hsize hmask hzero hnonzero heq hsupport hnorm hmissing
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have ha₀ : 51/100 ≤ a := by linarith
  have ha₁ : a ≤ 1 := by linarith
  have ha₂ : 1/2 ≤ a := by linarith
  have hT : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hc := hcount left u₀ unit Z hZ₂ q m a (3*(i+1 : ℕ)*Z^P.τ)
    hq ha ha' hT labels (fun l j => (D l).character j) dictionary puncture
    (fun _ _ => false) (fun l j => (D l).hcharacter j)
    hmask hzero hnonzero heq hsupport hnorm hmissing
  let xp := (2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N
  have hpoint : ∀ l ∈ labels, ‖(D l).row P‖^2 ≤ K*Z^xp := by
    intro l hl
    exact high_source_datum_cap M H P hZ.1.le hCs.le ha₂
      (hZ.2 a ha₀ ha₁ i (D l) (hvalid l hl)) (hsize l hl).1 (hsize l hl).2
  calc
    (∑ l ∈ labels, ‖(D l).row P‖^2) ≤ (labels.card:ℝ)*(K*Z^xp) := by
      simpa using Finset.sum_le_sum hpoint
    _ ≤ (Cd*(1+3*(i+1 : ℕ)*Z^P.τ)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss))*(K*Z^xp) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hK.le (Real.rpow_nonneg hZp.le _))
    _ = _ := by
      have hp : Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
          2*P.εplain*P.d+2*P.εslot*P.d*N) =
          Z^(m+q*unmarkedDensity (2*a-1)+loss)*Z^xp := by
        rw [←Real.rpow_add hZp]
        dsimp [xp]
        congr 1
        ring
      rw [hp]
      ring

#print axioms actual_joint_high_source_energy
#print axioms actual_high_source_datum
#print axioms high_source_datum_cap
end
end OAI.SevenEighths.Cycle63Moment
