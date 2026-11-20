/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual four divided canonical lengths, actual original row set and
original profile control. The only analytic premise is balanced raw sides. -/
import Candidate.C092.transport.OrderedPairActualRestoredRawFinite
import Candidate.C092.transport.OrderedPairActualRestoredCanonical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open HeckeInverseAmplification ConcreteTraceCRT CenteredMomentEnergyBands
open ProbeHighRowFamily CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedOriginalTail RepairedSourceSideSupply
open QRH.Cycle092.TwistedRawBall QRH.Cycle092.TwistedRawBallRootProducer
open QRH.Cycle092.FixedFramePacking
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local notation "Prime"=>QRH.Record1252270103KernelMass.PrimeIdeal

/-- Exact conversion of the original finite free rows; no keep is enlarged. -/
theorem free_rows_sum_image (rows:Finset FreeRow) (f:O→ℝ) :
    (∑u∈rows,f u.val)=∑z∈rows.image Subtype.val,f z := by
  exact (Finset.sum_image (fun u (_:u∈rows) v (_:v∈rows) h=>Subtype.val_injective h)).symm

/-- One early constant and threshold cover all genuine native remaining
slot types and all actual inverse divisors. All ball caps are proved inside. -/
theorem actual_canonical_divided_leaf (Slot:Type) [Fintype Slot] (J degree:ℕ)
    (W:ℝ→ℂ) (hW:Continuous W) (hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (controls:Finset (ℕ×ℕ)) (h00:(0,0)∈controls)
    (cRad ξ κ εmass εout:ℝ) (hcRad:1 ≤ cRad) (hξ:0<ξ) (hκ:0<κ)
    (hεmass:0<εmass) (hεout:0<εout) (η:Character) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(k:RootShape Slot)(M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
      (hHr:RayOrthogonality.globalUnits M ≤ Hr)
      (r:RestoredRootSource.Data M Hr (RootSlot k)),r.Z=Z → r.W=W →
    ∀(S:Finset Prime)(d:IdealPair)(X₁ X₂ Y₁ Y₂ M₁ M₂ n y l t₁ t₂ height loss:ℝ),
      sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      length Z X₁ ≤ n → length Z X₂ ≤ y →
      (∑i,r.w i) ≤ l → l ≤ sourceWidth n y →
      Z^(115/1000:ℝ) ≤ X₁ → Z^(115/1000:ℝ) ≤ X₂ →
      Z^(115/1000:ℝ) ≤ Y₁ → Z^(115/1000:ℝ) ≤ Y₂ →
      X₁*X₂=Y₁*Y₂ →
      X₁ ≤ M₁ → Y₁ ≤ M₁ → X₂ ≤ M₂ → Y₂ ≤ M₂ → M₁ ≤ Z → M₂ ≤ Z →
      d∈divisorPool (KernelRowPools.supportedRectangle S (9/4) M₁ M₂) →
      0 ≤ height → loss+εmass ≤ εout →
    ∀(hX₁:0<X₁/d.1.absNorm)(hX₂:0<X₂/d.2.absNorm)
      (hY₁:0<Y₁/d.1.absNorm)(hY₂:0<Y₂/d.2.absNorm)
      (hprod:(X₁/d.1.absNorm)*(X₂/d.2.absNorm)=(Y₁/d.1.absNorm)*(Y₂/d.2.absNorm))
      (hx₁:X₁/d.1.absNorm ≤ r.Z)(hx₂:X₂/d.2.absNorm ≤ r.Z)
      (hy₁:Y₁/d.1.absNorm ≤ r.Z)(hy₂:Y₂/d.2.absNorm ≤ r.Z),
    let s:=canonicalPairSource M Hr hHr r (X₁/d.1.absNorm) (X₂/d.2.absNorm)
      (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) t₁ t₂ hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂
    let A:=(r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree
    ∀η₁ η₂:Character,
      SummedRetainedRawSides s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) η
        (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
    ∀rows:Finset FreeRow,(∀u∈rows,rowNorm u ≤ Z) →
      (∑u∈rows,‖sourceSignedRow s (by norm_num)
        (CenteredMomentAllocatedNaturalRadial.naturalCharacter η u.val)
        (idealCoeff η₁) (idealCoeff η₂)‖^2) ≤ C*A*Z^(1+εout) := by
  let K:=RestoredRootSource.slotBound W hW hWs
  have hK:1 ≤ K:=(RestoredRootSource.slotBound_spec W hW hWs).1
  let Cp:=4*K^(2*Fintype.card Slot)
  have hCp:0<Cp:=by dsimp [Cp];positivity
  obtain ⟨C,hC,hbound⟩:=finite_root_raw_sides Slot J cRad Cp ξ κ εmass εout
    hcRad hCp hξ hκ hεmass hεout η
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,restored_caps (Fintype.card Slot)] with Z hb hc
  refine ⟨hc.1,?_⟩
  intro k M inst Hr hHr r hrZ hrW S d X₁ X₂ Y₁ Y₂ M₁ M₂ n y l t₁ t₂ height loss
    hy0 hy1 hn hxn hxy hsum hl hq₁ hq₂ hq₃ hq₄ hparentprod hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hd
    hheight hloss hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂
  dsimp only
  let s:=canonicalPairSource M Hr hHr r (X₁/d.1.absNorm) (X₂/d.2.absNorm)
    (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) t₁ t₂ hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂
  let A:=(r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree
  intro η₁ η₂ hprice rows hrad
  have hP:∀i,s.P i=Z^(r.w i):=by intro i;change r.Z^(r.w i)=_;rw [hrZ]
  have caps:=hc.2 (RootSlot k) s S d X₁ X₂ Y₁ Y₂ M₁ M₂ n y l r.w
    (root_slot_card k) r.hw hP hy0 hy1 hn hxn hxy hsum hl hq₁ hq₂ hq₃ hq₄
    hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hd rfl rfl rfl rfl rfl
  have hH:1 ≤ 1+|t₁|+|t₂|+height:=by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hpoly:1 ≤ (1+|t₁|+|t₂|+height)^degree:=one_le_pow₀ hH
  have hA:0 ≤ A:=mul_nonneg (sq_nonneg _) (by positivity)
  have hprofile:profileCap s^2 ≤ Cp*A:=by
    have hM:∀i,s.M i ≤ K:=by
      intro i
      change RestoredRootSource.slotBound r.W r.hW r.hWs ≤ K
      dsimp only [K]
      subst W
      exact le_rfl
    have hp:=profile_cap_sq s (Fintype.card Slot) (root_slot_card k) K hK hM r.p rfl rfl controls h00
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_right (sq_nonneg _) hpoly) hCp.le)
  have hrow:∀z∈rows.image Subtype.val,z≠0:=by
    intro z hz
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    exact u.property.1
  have hrad':∀z∈rows.image Subtype.val,‖eisEmbedding z‖^2 ≤ Z:=by
    intro z hz
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrad u hu
  rw [free_rows_sum_image rows (fun z=>‖sourceSignedRow s (by norm_num)
    (CenteredMomentAllocatedNaturalRadial.naturalCharacter η z) (idealCoeff η₁) (idealCoeff η₂)‖^2)]
  exact hb.2 k η₁ η₂ s
    (canonicalPairSource_original_enclosure M Hr hHr r _ _ _ _ t₁ t₂
      hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂)
    rfl rfl rfl n y r.w caps A loss hA hprofile hloss hprice _ hrow hrad'

#print axioms free_rows_sum_image
#print axioms actual_canonical_divided_leaf
end
end QRH.Cycle092.OrderedPairActualRestored
