/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.reserve_local_20261013.Bundles.B034
import Submissions.reserve_local_20261013.Bundles.B104
import Submissions.reserve_local_20261013.Bundles.B108
import Submissions.reserve_local_20261013.Bundles.B109
import Submissions.reserve_local_20261013.Bundles.B110
import Submissions.reserve_local_20261013.Bundles.B111
import Submissions.reserve_local_20261013.Bundles.B115
import Submissions.reserve_local_20261013.Bundles.B117

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAbsoluteFromAnnular ; sha256 bff3bd677af0af507f0a035ef985c7e96045b1d5f8a7bca092f0479d9e276d1a -/
section



/-! Assemble uniform annular energy targets into the absolute first
transform sum. The strict height gap pays all fixed Fourier shifts. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization
open CenteredMomentFirstAnnularMajorant CenteredMomentSecondRetainedRows CenteredMomentLogDyadic
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance firstAnnularTargetsDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem eventually_original_first_absolute_from_annular_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (Ncap : ℕ)
    (ν η F U b₁ b₂ B₁ B₂ a₁ a₂ aSource e Amin Amax : ℝ)
    (hν : 0 < ν) (hgap : ν < η) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (haSource : 0 < aSource) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i,s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x,‖s.W₁ x‖ ≤ B₁) → (∀ x,‖s.W₂ x‖ ≤ B₂) →
    (∀ x,s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x,s.W₂ x ≠ 0 → a₂ ≤ x) →
    aSource ≤ originalLowerProfile s a₁ a₂ →
    0 < sourceRadius s → sourceRadius s ≤ Z^(1:ℝ) →
    ∀ A : ℝ,Amin ≤ A → A ≤ Amax → volume s.toData = Z^A →
    ∀ ξ : ℝ,ξ ≤ 1 →
    let radius := actualLowFirstRadius s R 1 Z Z ξ
    let q := firstSourceOuterLabel s R 1 Z radius
    ∀ t Ch : ℝ,|t| ≤ Z^ν → 0 ≤ Ch →
    let live := firstLiveSourceLabels s R 1 Z radius Finset.univ (fun _ => t) Wkernel (fun _ => logAnnulus)
    (∀ (labels : Finset (FirstSourceOuterIndex s R 1 Z radius)),labels ⊆ live →
      ∀ ref ∈ labels,
      (∀ i ∈ labels,∀ j,|(q i).fullWidthCoordinates Z j-(q ref).fullWidthCoordinates Z j| < e) →
      (∀ i ∈ labels,(q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
        (q i).activeWidth Z/2+(q i).punctureWidth Z) →
      ∀ u : Bool → ((i : FirstSourceOuterIndex s R 1 Z radius) × (q i).SourceIndex) → ℝ,
      (∀ left,∀ k ∈ firstSourceLabels labels q,|u left k| ≤ Z^η) →
      ∀ left,
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).sideEnergy left (u left k) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/(((q ref).sideCommon left).absNorm : ℝ))*(Ch*Z^((q ref).sideTargetWidth left Z A))) →
    (∑ i : FirstSourceOuterIndex s R 1 Z radius,
      ‖firstPhysicalValue s R 1 Z radius (fun _ => t) Wkernel (fun _ => logAnnulus) i‖)/
      volume s.toData ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂
        (QuadraticInitialBound.diagonalControl profile))*Z^(1+e) := by
  obtain ⟨C,hC,habsolute⟩ := eventually_original_first_absolute_from_joint_targets
    (ι := ι) Wkernel Ncap ν F U b₁ b₂ B₁ B₂ a₁ a₂ aSource e Amin Amax
    hν hB₁ hB₂ ha₁ ha₂ haSource he
  refine ⟨C,hC,?_⟩
  filter_upwards [habsolute,eventually_first_fourier_targets_of_annular ν η hgap] with Z habsolute hfourier
  intro s R hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hs₁ hs₂ haProfile hsourcepos hsource
    A hAmin hAmax hvolume ξ hξ
  dsimp only
  intro t Ch ht hCh hannular
  apply habsolute s R hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hs₁ hs₂ haProfile
    hsourcepos hsource A hAmin hAmax hvolume ξ hξ t Ch hCh
  intro labels hlabels ref href hclose hmin
  exact hfourier labels (firstSourceOuterLabel s R 1 Z (actualLowFirstRadius s R 1 Z Z ξ))
    (firstSourceOuterLabel s R 1 Z (actualLowFirstRadius s R 1 Z Z ξ) ref)
    (fun _ => t) (fun i => dyadicScale (i.2.2 1)) (Z^A) A Ch (fun _ _ => ht)
    (hannular labels hlabels ref href hclose hmin)

#print axioms eventually_original_first_absolute_from_annular_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAbsoluteFromAnnular -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalJoinGates ; sha256 b4d7c83d99dcfc0e3c3fb29225f6c3f65c9dfe28a10b099d79f0e70e94eba8a3 -/
section




/-! Geometry of the literal quarter-centered natural source. The eventual
threshold depends only on fixed support endpoints and the number of slots,
and is uniform in the two plain profiles. Their pointwise norms are bounded
by their own explicit Schwartz seminorms; no uniform norm bound over all
`Profiles a b` is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData CenteredMomentSourceRow CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyNaturalInputMatches CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

namespace LocalFirstNaturalSource
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance naturalJoinFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable (η₀ : Character) (θ : α → RayQuotient.Characters M H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Icc aslot bslot)
variable (w σ freq : α → ℝ) (hσ : ∀ i,σ i ∈ Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (s : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "src" => input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

theorem plain_join_gates :
    (src).W₁ 0=0 ∧ (src).W₂ 0=0 ∧
    (∀ x,‖(src).W₁ x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (p.profile 0)) ∧
    (∀ x,‖(src).W₂ x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (p.profile 1)) ∧
    (∀ x,(src).W₁ x ≠ 0 → a ≤ x) ∧
    (∀ x,(src).W₂ x ≠ 0 → a ≤ x) := by
  have hzero (i : Fin 2) : p.profile i 0=0 := by
    by_contra hn
    have hh := (p.support i hn).1
    linarith only [ha,hh]
  exact ⟨hzero 0,hzero 1,SchwartzMap.norm_le_seminorm ℝ _,
    SchwartzMap.norm_le_seminorm ℝ _,fun x hx => (p.support 0 hx).1,
    fun x hx => (p.support 1 hx).1⟩

theorem lower_profile_exact :
    originalLowerProfile src a a = aslot^Fintype.card α*a^2 := by
  change (∏ _i : α,aslot)*a*a = _
  simp only [Finset.prod_const,Finset.card_univ]
  ring

include haslot ha in
theorem lower_profile_positive : 0 < aslot^Fintype.card α*a^2 := by positivity

end LocalFirstNaturalSource

/-- The nonnegative length, capacity and support gates required by the
annular and absolute first-source joins. All are conclusions for the
literal source, rather than independent admissibility assumptions. -/
structure FirstNaturalJoinGeometry {α : Type*} [Fintype α]
    (src : Input α) (Z A : ℝ) (w : α → ℝ) : Prop where
  volume_log : A = Real.logb Z (src).X₁+Real.logb Z (src).X₂+∑ i,w i
  volume_eq : volume (src).toData = Z^A
  width_nonneg : 0 ≤ A
  width_upper : A ≤ 881/1000
  source_positive : 0 < sourceRadius src
  source_cap : sourceRadius src ≤ Z
  source_width : sourceRadius src ≤ Z^(A+lowLocalTiny)
  prime_scales : ∀ i,1 ≤ (src).P i ∧ (src).P i ≤ Z^lowLocalMesh
  support_power : (max 1 (src).upper)^Fintype.card α ≤ Z^lowLocalTiny
  clipping : Real.logb Z (max 1 (src).b₁*max 1 (src).b₂) ≤ 2*lowLocalTiny
  old_capacity : A+(7/2)*(∑ i,w i) ≤
    1+max (Real.logb Z (src).X₁+Real.logb Z (src).X₂+(9/2)*(∑ i,w i)-1) 0
  defect_nonneg : 0 ≤ max (Real.logb Z (src).X₁+Real.logb Z (src).X₂+(9/2)*(∑ i,w i)-1) 0
  defect_upper : max (Real.logb Z (src).X₁+Real.logb Z (src).X₂+(9/2)*(∑ i,w i)-1) 0 ≤ 1/250
  comparison_upper : Real.logb Z (src).Y₁ ≤ 1 ∧ Real.logb Z (src).Y₂ ≤ 1
  rectangle_lower : Z^(1/4:ℝ) ≤ (src).X₁ ∧ Z^(1/4:ℝ) ≤ (src).X₂ ∧
    Z^(1/4:ℝ) ≤ (src).Y₁ ∧ Z^(1/4:ℝ) ≤ (src).Y₂

namespace LocalFirstNaturalSource
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance naturalJoinEventualFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The threshold is uniform in the natural state, anchors, ray characters,
slot shifts and both plain profiles. Only their fixed support endpoints
enter the geometric constants. -/
theorem eventually_join_geometry
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi a b : ℝ)
    (haslot : 0 < aslot) (hbslot : 0 < bslot)
    (hWs : Function.support W ⊆ Icc aslot bslot) (ha : 0 < a) (hb : 1 ≤ b) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (θ : α → RayQuotient.Characters M H)
      (w σ freq : α → ℝ) (hσ : ∀ i,σ i ∈ Icc lo hi)
      (Bmask bΦ : ℝ) (s : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ lowLocalMesh) →
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
      let src := input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂;
      FirstNaturalJoinGeometry src Z (Real.logb Z (volume (src).toData)) w := by
  have htiny : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  filter_upwards [eventually_low_fixed_profile_gates (ι := α) bslot b b b lowLocalTiny htiny]
    with Z hfixed
  refine ⟨hfixed.1,?_⟩
  intro η₀ θ w σ freq hσ Bmask bΦ s p t X₁ X₂ hX₁ hX₂ hw hwcap
    hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity
  let src := input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂
  have hZ := hfixed.1
  have hz := zero_lt_one.trans hZ
  have hsource := source_radius_positive M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ hbslot (zero_lt_one.trans_le hb)
  have hgeom := hfixed.2.1 src hsource
    (fun _ => by change |bslot| ≤ bslot;rw [abs_of_pos hbslot])
    (by change |b| ≤ b;rw [abs_of_nonneg (zero_le_one.trans hb)])
    (by change |b| ≤ b;rw [abs_of_nonneg (zero_le_one.trans hb)]) le_rfl
  have hlog := original_volume_log src Z w hZ (fun _ => rfl)
  have hcap := local_capacity_of_volume Z (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i)
    (Real.logb Z (volume (src).toData)) hlog hn₁hi hn₂hi hsum hcapacity
  have hnorm : 0 ≤ Real.logb Z (volume (src).toData) := by
    rw [hlog]
    change 0 ≤ Real.logb Z X₁+Real.logb Z X₂+∑ i,w i
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => hw i)]
  have hsourceWidth : sourceRadius src ≤ Z^(Real.logb Z (volume (src).toData)+lowLocalTiny) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb hz hZ.ne' hsource).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hgeom.1
  have hsourceCap : sourceRadius src ≤ Z := by
    apply hsourceWidth.trans
    calc
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by
        have hh := hcap.1
        norm_num [lowLocalTiny] at ⊢
        linarith only [hh])
      _ = Z := Real.rpow_one Z
  have hprofile : (max 1 (src).upper)^Fintype.card α ≤ Z^lowLocalTiny := by
    have hh := hgeom.2
    rw [←Real.logb_pow] at hh
    calc
      _ = Z^(Real.logb Z ((max 1 (src).upper)^Fintype.card α)) :=
        (Real.rpow_logb hz hZ.ne' (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hh
  have hcompare := comparison_source_gates M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ hZ hn₁lo hn₂lo hn₁hi hn₂hi
  exact {
    volume_log := hlog
    volume_eq := (Real.rpow_logb hz hZ.ne' (volume_pos (src).toData)).symm
    width_nonneg := hnorm
    width_upper := hcap.1
    source_positive := hsource
    source_cap := hsourceCap
    source_width := hsourceWidth
    prime_scales := fun i => ⟨Real.one_le_rpow hZ.le (hw i),
      Real.rpow_le_rpow_of_exponent_le hZ.le (hwcap i)⟩
    support_power := hprofile
    clipping := hfixed.2.2.1
    old_capacity := hcap.2.1
    defect_nonneg := hcap.2.2.1
    defect_upper := hcap.2.2.2
    comparison_upper := ⟨hcompare.1,hcompare.2.1⟩
    rectangle_lower := hcompare.2.2 }

end LocalFirstNaturalSource
#print axioms LocalFirstNaturalSource.plain_join_gates
#print axioms LocalFirstNaturalSource.lower_profile_exact
#print axioms LocalFirstNaturalSource.eventually_join_geometry
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalJoinGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalTarget ; sha256 927a916e62615f63b5aedaada12e203b00ab322c996f9453c42e2f78bd97fab5 -/
section


set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance firstNaturalTargetAlphaDecEq : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance firstNaturalTargetFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

/-- Original fixed-parent natural energy reduces to the literal retained first
blocks with every zero, discarded and comparison contribution already bounded. -/
theorem actual_local_first_natural_target
    (Wslot:ℝ→ℂ)(aslot bslot lo hi a b bΦ Bmask ε ξ:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hcSlot:ContDiff ℝ ∞ Wslot)(hbslot:0< bslot)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hBmask:0≤ Bmask)(hε:0<ε)(hξ:0<ξ)
    (hbeta:51/100≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8):
    ∃mesh:ℝ,0< mesh ∧ ∃J:ℕ,∃U Sd St:Finset (ℕ×ℕ),∃Cd Ct:ℝ,0< Cd ∧ 0< Ct ∧
    ∀ηfirst η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cc:ℝ,0< Cc ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height → (∀i,|freq i|≤ height) →
      ∀(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      410/1000≤ Real.logb Z X₁ → 410/1000≤ Real.logb Z X₂ →
      Real.logb Z X₁≤423/1000 → Real.logb Z X₂≤423/1000 → (∑i,w i)≤37/1000 →
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀ →
        s.character=ηfirst → s.rowWidth=1 →
        s.characterWidth=Real.logb Z (ηfirst.modulus.absNorm:ℝ) →
      ∀p:Profiles a b,
      let src:=LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
        aslot bslot lo hi haslot hsSlot w σ freq (fun i=>⟨hσlo i,hσhi i⟩)
        s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (2/volume src.toData)*
        (∑i:FirstSourceOuterIndex src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ),
          ‖firstPhysicalValue src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ)
            (fun _=> t) s.radial.profile (fun _=> logAnnulus) i‖)+
      2*Cd*(plainControl src (p.profile 0) (p.profile 1))^2*
        Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) s.radial.profile*Z^(1+ε)+
      2*Ct*(plainControl src (p.profile 0) (p.profile 1))^2*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) s.radial.profile*Z^(1+ε)+
      2*Cc*diagonalControl s.radial.profile*
        (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(1+ε):=by
  obtain ⟨mesh,hmesh,J,U,Sd,St,Cd,Ct,hCd,hCt,hbound⟩:=actual_local_first_original_target
    (α:=α) M H hH Wslot aslot bslot lo hi a b bΦ Bmask bslot b b ε ξ
    haslot hsSlot hcSlot hbslot.le ha hlo hhi hbΦ hBmask hbslot.le hε hξ hbeta hbetaTop
  refine ⟨mesh,hmesh,J,U,Sd,St,Cd,Ct,hCd,hCt,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72
  obtain ⟨Cc,hCc,hbound⟩:=hbound ηfirst η₀ Q hQM hQzero hQtop hQ72
  refine ⟨Cc,hCc,?_⟩
  filter_upwards [hbound] with Z hb
  refine ⟨hb.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hheight hfreq X₁ X₂ hX₁ hX₂
    hn₁lo hn₂lo hn₁hi hn₂hi hslots s hQ hη hrow hwidth p
  let src:=LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i=>⟨hσlo i,hσhi i⟩)
    s p ha t X₁ X₂ hX₁ hX₂
  have hsource:0< sourceRadius src:=LocalFirstNaturalSource.source_radius_positive
    M H hH η₀ θ Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot w σ freq
    (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ hbslot (by linarith)
  have hm:=LocalFirstNaturalSource.input_matches M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i=>⟨hσlo i,hσhi i⟩)
    s p ha t X₁ X₂ hX₁ hX₂
  exact hb.2 src p rfl rfl (fun _=> by change |bslot|≤ bslot;rw [abs_of_pos hbslot])
    (by change |b|≤ b;rw [abs_of_nonneg (by linarith)])
    (by change |b|≤ b;rw [abs_of_nonneg (by linarith)]) le_rfl hsource
    θ w σ freq height hm hw hwmesh hσlo hσhi hheight hfreq
    hn₁lo hn₂lo hn₁hi hn₂hi hslots rfl rfl s hQ hη rfl hrow hwidth

#print axioms actual_local_first_natural_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalTargetExplicitMesh ; sha256 6aee791d1386167cfca25a290c490e369d523c7efead31a0bc011fdbc3fd5d03 -/
section



set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance firstNaturalExplicitAlphaDecEq : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance firstNaturalExplicitFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

/-- Original fixed-parent natural energy reduces to the literal retained first
blocks with every zero, discarded and comparison contribution already bounded. -/
theorem actual_local_first_natural_target_explicit_mesh
    (Wslot:ℝ→ℂ)(aslot bslot lo hi a b bΦ Bmask ε ξ:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hcSlot:ContDiff ℝ ∞ Wslot)(hbslot:0< bslot)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hBmask:0≤ Bmask)(hε:0<ε)(hξ:0<ξ)
    (hbeta:51/100≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8):
    ∃J:ℕ,∃U Sd St:Finset (ℕ×ℕ),∃Cd Ct:ℝ,0< Cd ∧ 0< Ct ∧
    ∀ηfirst η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cc:ℝ,0< Cc ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ meshGuaranteed Bmask ε) →
      ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height → (∀i,|freq i|≤ height) →
      ∀(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      410/1000≤ Real.logb Z X₁ → 410/1000≤ Real.logb Z X₂ →
      Real.logb Z X₁≤423/1000 → Real.logb Z X₂≤423/1000 → (∑i,w i)≤37/1000 →
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀ →
        s.character=ηfirst → s.rowWidth=1 →
        s.characterWidth=Real.logb Z (ηfirst.modulus.absNorm:ℝ) →
      ∀p:Profiles a b,
      let src:=LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
        aslot bslot lo hi haslot hsSlot w σ freq (fun i=>⟨hσlo i,hσhi i⟩)
        s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (2/volume src.toData)*
        (∑i:FirstSourceOuterIndex src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ),
          ‖firstPhysicalValue src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ)
            (fun _=> t) s.radial.profile (fun _=> logAnnulus) i‖)+
      2*Cd*(plainControl src (p.profile 0) (p.profile 1))^2*
        Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) s.radial.profile*Z^(1+ε)+
      2*Ct*(plainControl src (p.profile 0) (p.profile 1))^2*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) s.radial.profile*Z^(1+ε)+
      2*Cc*diagonalControl s.radial.profile*
        (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(1+ε):=by
  obtain ⟨J,U,Sd,St,Cd,Ct,hCd,hCt,hbound⟩:=actual_local_first_original_target_explicit_mesh
    (α:=α) M H hH Wslot aslot bslot lo hi a b bΦ Bmask bslot b b ε ξ
    haslot hsSlot hcSlot hbslot.le ha hlo hhi hbΦ hBmask hbslot.le hε hξ hbeta hbetaTop
  refine ⟨J,U,Sd,St,Cd,Ct,hCd,hCt,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72
  obtain ⟨Cc,hCc,hbound⟩:=hbound ηfirst η₀ Q hQM hQzero hQtop hQ72
  refine ⟨Cc,hCc,?_⟩
  filter_upwards [hbound] with Z hb
  refine ⟨hb.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hheight hfreq X₁ X₂ hX₁ hX₂
    hn₁lo hn₂lo hn₁hi hn₂hi hslots s hQ hη hrow hwidth p
  let src:=LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i=>⟨hσlo i,hσhi i⟩)
    s p ha t X₁ X₂ hX₁ hX₂
  have hsource:0< sourceRadius src:=LocalFirstNaturalSource.source_radius_positive
    M H hH η₀ θ Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot w σ freq
    (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ hbslot (by linarith)
  have hm:=LocalFirstNaturalSource.input_matches M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i=>⟨hσlo i,hσhi i⟩)
    s p ha t X₁ X₂ hX₁ hX₂
  exact hb.2 src p rfl rfl (fun _=> by change |bslot|≤ bslot;rw [abs_of_pos hbslot])
    (by change |b|≤ b;rw [abs_of_nonneg (by linarith)])
    (by change |b|≤ b;rw [abs_of_nonneg (by linarith)]) le_rfl hsource
    θ w σ freq height hm hw hwmesh hσlo hσhi hheight hfreq
    hn₁lo hn₂lo hn₁hi hn₂hi hslots rfl rfl s hQ hη rfl hrow hwidth

#print axioms actual_local_first_natural_target_explicit_mesh
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalTargetExplicitMesh -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLocalBound ; sha256 c609f91755aa9eaa9a41178496cb685ad1787d4d7f4efc49aa2767d483c569d2 -/
section







/-! The fixed local high estimate: all numerical losses and Mellin budgets
are chosen before the live source. Only the literal source-data constructor
is used for each nonempty packet cell and first-ray pair. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O

variable {Cell κbin : Type*} [Fintype Cell] [DecidableEq Cell] [DecidableEq κbin]
section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : Q ≤ η₀.modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_local_high_reference_bound
    (Wslot : ℝ → ℂ) (aslot bslot : ℝ) (haslot : 0 < aslot)
    (hWslot : ContDiff ℝ ∞ Wslot)
    (hslotSupport : Function.support Wslot ⊆ Icc aslot bslot)
    (BR e σmin σmax τdetector : ℝ) (I : ℕ)
    (hBR : 0 ≤ BR) (he : 0 < e) (hecap : e ≤ highLocalBinCap BR (Fintype.card Slot))
    (hτdetector : 0 < τdetector)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (hlo : ∀ j,0 < lo j)
    (Mslot upper : ℝ) (hMslot : 0 ≤ Mslot)
    (Sbad : Finset (Ideal O)) (Wkernel : 𝓢(ℝ,ℂ)) :
    ∃ τ ν C : ℝ, 0 < ν ∧ ν < τ ∧ τ < τdetector ∧
      4*τ < highLocalEpsilon BR (Fintype.card Slot)/16 ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (src : Input Slot) (Rmask seed : Ideal O) (hs : Squarefree seed)
        (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0) (Kfirst : ℝ)
        (radius : (p : Labels src Rmask seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
        (side : Bool) (A Mparent omega ξ : ℝ)
        (bin : NonzeroElement → Option κbin) (bidx : κbin)
        (height : First src Rmask seed Kfirst radius → ℝ)
        (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius))
        (cell : LivePacket src Rmask seed Kfirst radius side Z A Mparent omega ξ → Cell)
        (ref : FirstJointLabel Slot),
      0 < actualHighPrimeCount M H Sbad Z →
      let X := liveBinPackets src Rmask seed Kfirst radius side Z A Mparent omega ξ hs hz₁ hz₂
        bin bidx height Wkernel labels;
      (∀ c : Cell, ∀ χ₁ ξ₁ : RayCharacter,
        (rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁).Nonempty →
        ∃ actualExponent : ℝ, LocalHighPacketData M H hH η η₀ Q hQ72 hQM hQη₀
          Wslot bslot BR e σmin σmax I W₁ W₂ b₁ b₂plain lo hi Mslot upper Sbad Wkernel Z τ ν
          (∑ x∈rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁,
            packetValue hs hz₁ hz₂ (CenteredMomentExceptionalAmplitudePair.volume src.toData)
              (actualHighPrimeCount M H Sbad Z) height Wkernel x) actualExponent ∧ actualExponent ≤ ref.radicalWidth Z+A-2*ref.sideWidth side Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance side Z-1/10000) →
      (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src Rmask seed Kfirst radius)
        (fun _ => sourceRadius src) side,
        ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k side Z A Mparent omega ξ
          (height k) Wkernel bin bidx‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
        (C /
          ((ref.sideCommon side).absNorm : ℝ))*Z^(ref.sideTargetWidth side Z A-1/10000) := by
  obtain ⟨hdmax,hε,hbin,hparameters⟩ := high_local_product_parameters BR (Fintype.card Slot) hBR
  obtain ⟨helow,hesmall,hκ,hκone,hη,hbudget,hprimebudget,hproduct,hpaid⟩ := hparameters e he hecap
  have htiny : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  have hsource : 0 < (∏ j,lo j)*a₁*a₂ :=
    mul_pos (mul_pos (Finset.prod_pos (fun j _ => hlo j)) ha₁) ha₂
  obtain ⟨B₁,hB₁⟩ := (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs₁).exists_bound_of_continuous hW₁.continuous
  obtain ⟨B₂,hB₂⟩ := (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs₂).exists_bound_of_continuous hW₂.continuous
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_first_high_reference_target (Cell := Cell) (κbin := κbin)
      η (fun _ : Slot => η₀) Q hQtop hQ72 hQη hβ M H hH hQM (fun _ => hQη₀) S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      (fun _ : Slot => Wslot) (fun _ => aslot) (fun _ => bslot)
      (fun _ => haslot) (fun _ => hslotSupport) (fun _ => hWslot)
      η₀ (fun _ => rfl) Wslot (fun _ => rfl) bslot (fun _ => rfl)
      2 (highLocalDmax BR) (highLocalEpsilon BR (Fintype.card Slot)) e
      (highLocalEpsilon BR (Fintype.card Slot)/32)
      (highLocalEpsilon BR (Fintype.card Slot)/16) σmin σmax
      (highLocalProductLoss BR (Fintype.card Slot)) (lowLocalTiny/2) lowLocalTiny 6
      (by norm_num) (by linarith only [hdmax]) hε he hesmall hκ hκone hη hbudget hprimebudget hproduct
      (by positivity) (by norm_num) hpaid
      τdetector 1 lowLocalTiny I hτdetector (by norm_num) htiny
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi lowLocalTiny htiny
      ((∏ j,lo j)*a₁*a₂) Mslot upper hsource hMslot lowLocalTiny htiny
      Sbad lowLocalTiny htiny (by norm_num [lowLocalTiny]) Wkernel 4 (-2) (max 0 B₁) (max 0 B₂)
      (le_max_left _ _) (le_max_left _ _)
      (fun x => (hB₁ x).trans (le_max_right _ _))
      (fun x => (hB₂ x).trans (le_max_right _ _))
      1 3 1 1 6 1 lowLocalTiny
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) htiny
      lowLocalTiny htiny rfl
  let C' := (1+(Fintype.card Cell : ℝ)*(Fintype.card RayCharacter : ℝ)^2)*C
  have hC' : 0 < C' := mul_pos (by positivity) hC
  refine ⟨τ,ν,C',hν,hντ,hτdet,by simpa only [one_mul] using hheight,hC',?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src Rmask seed hs hz₁ hz₂ Kfirst radius side A Mparent omega ξ bin bidx height labels cell ref hP X hdata
  have hh := hZ.2 src Rmask seed hs hz₁ hz₂ Kfirst radius side A Mparent omega ξ
    bin bidx height labels cell ref hP hdata
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  dsimp only [C']
  nlinarith only [hC]

end FixedData
#print axioms actual_local_high_reference_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLocalBound -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighReferenceGates ; sha256 1112fe5b37b39f05f7cc4af63469517b63bf5b033652b225cc3c4d141d2b735e -/
section


/-! The high ledger's reference inequalities follow from the literal
first common ideals and their cancellation factors, on either side. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstSourceConductorCaps CenteredMomentSectorLocalization
open CenteredMomentFirstMixedRoot CenteredMomentSupportedCorrelation
local notation "O" => HeckeFamily.O
namespace FirstJointLabel
variable {Slot : Type*} [Fintype Slot]

theorem high_radical_reference (q : FirstJointLabel Slot) (Z : ℝ) (hZ : 1 < Z) (left : Bool) :
    0 ≤ q.radicalWidth Z ∧ q.radicalWidth Z ≤ q.sideWidth left Z ∧
    q.radicalWidth Z ≤ q.sideWidth (!left) Z ∧ q.activeWidth Z ≤ q.radicalWidth Z := by
  have hrad : commonRadical q.C q.D ≠ 0 := commonRadical_ne_zero _ _
  have hswap : commonRadical q.D q.C = commonRadical q.C q.D := by
    unfold commonRadical
    rw [Finset.inter_comm]
  have hNC : ((commonRadical q.C q.D).absNorm : ℝ) ≤ q.C.absNorm :=
    divisor_norm_le _ _ q.hC.1 ((commonRadical_dvd_commonPart q.C q.D).trans (commonPart_dvd q.C q.D q.hC.1))
  have hND : ((commonRadical q.C q.D).absNorm : ℝ) ≤ q.D.absNorm := by
    rw [←hswap]
    exact divisor_norm_le _ _ q.hD.1 ((commonRadical_dvd_commonPart q.D q.C).trans (commonPart_dvd q.D q.C q.hD.1))
  have hNA : ((Ideal.span {activeConductor q.C q.D}).absNorm : ℝ) ≤ (commonRadical q.C q.D).absNorm :=
    divisor_norm_le _ _ hrad ⟨_,commonRadical_active_principal q.C q.D⟩
  have hp₀ := CenteredMomentFirstScale.norm_pos _ hrad
  have ha₀ := CenteredMomentFirstScale.active_norm_pos q.C q.D
  have hc := Real.logb_le_logb_of_le hZ hp₀ hNC
  have hd := Real.logb_le_logb_of_le hZ hp₀ hND
  have ha := Real.logb_le_logb_of_le hZ ha₀ hNA
  refine ⟨(q.target_auxiliary_widths_nonneg Z hZ).1,?_,?_,ha⟩
  · cases left <;> assumption
  · cases left <;> assumption

theorem high_cancellation_reference (q : FirstJointLabel Slot) (left : Bool) (Z : ℝ) (hZ : 1 < Z) :
    let L := Real.logb Z (normValue (leftEffectiveFactor (q.sideCommon left) (q.sideCommon (!left))))
    let R₀ := Real.logb Z ((canceledIdeal (q.sideCommon left) (q.sideCommon (!left)) 5).absNorm : ℝ)
    0 ≤ L ∧ 0 ≤ R₀ ∧ R₀ ≤ q.activeWidth Z ∧ L ≤ 5*(q.activeWidth Z-R₀) := by
  have hh := left_cancellation_coordinates (q.sideCommon left) (q.sideCommon (!left))
    (q.sideCommon_supported left) Z hZ
  have heq : Real.logb Z (normValue (activeConductor (q.sideCommon left) (q.sideCommon (!left)))) =
      q.activeWidth Z := by
    cases left
    · simp only [sideCommon,Bool.not_false,Bool.false_eq_true,if_false,if_true,normValue,active_span_swap]
      rfl
    · rfl
  simpa only [heq] using hh

theorem high_reference_caps (q : FirstJointLabel Slot) (left : Bool) (Z : ℝ) (hZ : 1 < Z)
    (hC : (q.C.absNorm : ℝ) ≤ Z^(1:ℝ)) (hD : (q.D.absNorm : ℝ) ≤ Z^(1:ℝ)) :
    0 ≤ q.sideWidth left Z ∧ q.sideWidth left Z ≤ 1 ∧
    0 ≤ q.sideWidth (!left) Z ∧ q.sideWidth (!left) Z ≤ 1 ∧
    0 ≤ q.radicalWidth Z ∧ q.radicalWidth Z ≤ 1 ∧
    0 ≤ q.activeWidth Z ∧ q.activeWidth Z ≤ 1 ∧
    0 ≤ q.punctureWidth Z ∧ q.punctureWidth Z ≤ 1 ∧ 0 ≤ q.sideAllowance left Z := by
  have hc := q.sideWidth_bounds left Z 1 hZ hC hD
  have hd := q.sideWidth_bounds (!left) Z 1 hZ hC hD
  have hr := q.high_radical_reference Z hZ left
  have hn := q.target_auxiliary_widths_nonneg Z hZ
  have heN : ((Ideal.span {q.puncture}).absNorm : ℝ) ≤ q.C.absNorm :=
    divisor_norm_le _ _ q.hC.1 ((subsetGenerator_span_dvd q.C q.D q.E).trans (commonPart_dvd q.C q.D q.hC.1))
  have he₀ := CenteredMomentFirstScale.norm_pos _ (subsetGenerator_supported q.C q.D q.hC q.E).1
  have he := Real.logb_le_logb_of_le hZ he₀ (heN.trans hC)
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at he
  have he' : q.punctureWidth Z ≤ 1 := by
    simpa only [punctureWidth,puncture,eisEmbedding_norm_sq_eq_absNorm_span] using he
  refine ⟨hc.1,hc.2,hd.1,hd.2,hr.1,hr.2.1.trans hc.2,hn.2.1,
    hr.2.2.2.trans (hr.2.1.trans hc.2),hn.2.2.1,he',?_⟩
  cases left
  · exact hn.2.2.2.2
  · exact hn.2.2.2.1

end FirstJointLabel
#print axioms FirstJointLabel.high_radical_reference
#print axioms FirstJointLabel.high_cancellation_reference
#print axioms FirstJointLabel.high_reference_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighReferenceGates -/
