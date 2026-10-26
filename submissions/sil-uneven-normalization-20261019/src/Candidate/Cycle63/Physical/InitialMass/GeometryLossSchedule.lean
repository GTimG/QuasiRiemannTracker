import Candidate.Cycle63.Physical.InitialMass.GeometryMainTail
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPayment
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondSplit
import Candidate.Cycle63.Arithmetic.LocalReserves
import Candidate.Cycle63.Moment.HighParameters

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryMainRemainder. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentSupportedTailAggregate CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
local instance mainRemainderDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

open EisensteinSchwartzPoisson CenteredMomentSecondLocalization
/-- The complete literal weighted second zero sum is paid from its actual
first-column mass. Both physical-D factors and the seed saving are retained.
Constants precede the original profiles, source, labels, allocations and height. -/
theorem eventual_actual_geometry_main_zero_with_window {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (Cs bs lo hi slotlo Amax B U ξ εzero εmass εcount : ℝ)
    (hCs : 1≤Cs) (hbs : 1≤bs) (hlo : 0<lo) (hhi : 0≤hi) (hslotlo : 0<slotlo)
    (hAmax : 0≤Amax) (hB : 0≤B) (hU : 0≤U) (hξ : 0≤ξ)
    (hez : 0<εzero) (hem : 0<εmass) (hec : 0<εcount) :
    ∃Czero : ℝ, 0<Czero ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → s.upper≤bs → slotlo≤s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1<Z),
      3401/100000≤beta ∧ beta≤1/25 → 0≤M →
      (Real.logb Z (volume s))≤M*Cycle63.Arithmetic.totalA beta →
      a≤M*Cycle63.Arithmetic.amp beta → (Real.logb Z (volume s))≤Amax →
      bs^N≤Z^padding → Squarefree seed → seed≠0 →
      0<sourceRadius s → sourceRadius s≤Z^B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let source := fun (j : rows)(alloc : actualAllocations s.pools (C j))=>
      child s (C j) R alloc (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let factor := if reflected then 1/geometryDCompensator key else
      2*(geometrySupportConstant N slotlo lo lo)^2*geometryDCompensator key
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val alloc/
        volume (source j alloc))*‖originalSecondZero (source j alloc) (R*C j) j.val.2.1.val Φ
          (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
            (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val))‖)≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*factor*
        Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/
          (seed.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hfamily⟩ := actual_geometry_zero_family N Cs bs lo hi εzero εmass
    hCs hbs hlo hhi hez hem
  obtain ⟨C,hC,hpayment⟩ := eventual_actual_geometry_zero_mass_payment (ι:=ι)
    Amax 0 B (((N:ℝ)+2)*U) ξ εcount hAmax (by norm_num) hB (by positivity) hξ hec
    N slotlo lo lo hslotlo hlo hlo
  refine ⟨K₀*C,mul_pos hK₀ hC,?_⟩
  filter_upwards [hpayment] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ beta M a reserve padding t hZ
    hb hM hA ha hA' hgeo hseed hseed0 hsource hcap hpool reflected key hK A rows Cj source weight factor
  have hs₁ : ∀x,s.W₁ x≠0→lo≤x := by
    intro x hx; rw [hp₁] at hx; exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→lo≤x := by
    intro x hx; rw [hp₂] at hx; exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos s)).symm
  have hVcap : volume s≤Z^Amax := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hZ.le hA'
  have hKi : (Z^M)⁻¹≤Z^(0:ℝ) := by
    rw [Real.rpow_zero]
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow hZ.le hM
  have hrows : rows⊆firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus) :=
    Finset.Subset.refl _
  have hprojector : ∀r∈rows,(r.2.1.val.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
    intro r hr
    exact actual_geometry_projector_cap s N R seed (Z^M) Z ξ U hK hn hZ.le hU hpool key r
  have hzero := hfamily s hn hm hs p hp₁ hp₂ Φ reflected R seed Z beta M A a ξ reserve padding
    hZ hb hM hA ha hV hgeo key weight rows t
  have hmass := hz.2 s R seed W M a reserve padding εzero εmass hZ hn hl hez.le hem.le
    hseed hseed0 hz₁ hz₂ hsource hcap hVcap hKi hs₁ hs₂ reflected key rows hrows hprojector
  apply hzero.trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖)).trans_eq
  ring


/-- The actual amplified main source is reduced to its single joint retained
sum. The full zero and discarded contributions are paid uniformly from the
original profiles, with the physical-D and seed factors preserved. -/
theorem eventual_actual_geometry_main_remainder {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εzero εmass εcount saving : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hlo : 0<lo)(hhi : 0≤hi)(hslotlo : 0<slotlo)
    (hB : 0≤B)(hU : 0≤U)(hξ : 0<ξ)(hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → s.upper≤b → slotlo≤s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1<Z),
      3401/100000≤beta ∧ beta≤1/25 →
      0≤M → M≤B → 0≤a → a≤B → 0≤reserve →
      frequencyLoss Z 32 ξ+reserve≤B →
      Real.logb Z (volume s)≤M*Cycle63.Arithmetic.totalA beta →
      a≤M*Cycle63.Arithmetic.amp beta → b^N≤Z^padding →
      Squarefree seed → seed≠0 →
      0<sourceRadius s → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let source := fun (j : rows)(alloc : actualAllocations s.pools (C j))=>
      child s (C j) R alloc (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t
    let radius := fun j : rows=>firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
    let Fourier := fun j : rows=>firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*a) reserve b N
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let scalar : (j : rows) → actualAllocations s.pools (C j) → ℝ := fun j alloc=>
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),scalar j alloc*
      actualMainSource (source j alloc) (geometryBranch reflected s R seed (Z^M) Z ξ hK key j.val)
        Z (3*a) 1 ξ reserve)≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier ballProfile 0‖*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ)+
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(-saving)/(seed.absNorm:ℝ)+
      ‖∑j : rows,∑alloc : actualAllocations s.pools (C j),
        ((scalar j alloc/volume (source j alloc):ℝ):ℂ)*
          secondRetainedEnergy (source j alloc).η (source j alloc).t
            (original (source j alloc) (R*C j) j.val.2.1.val).columns
            (original (source j alloc) (R*C j) j.val.2.1.val).beta
            ballProfile (radius j) (Fourier j) Z ξ‖ := by
  obtain ⟨F,Ct,hCt,htail⟩ := eventual_actual_geometry_main_tail (ι:=ι)
    N Cs b lo hi slotlo B U ξ εmass εcount saving hCs hb hlo hhi hslotlo hB hU hξ hem hec
  obtain ⟨Cz,hCz,hzero⟩ := eventual_actual_geometry_main_zero_with_window (ι:=ι)
    N Cs b lo hi slotlo B B U ξ εzero εmass εcount hCs hb hlo hhi hslotlo hB hB hU hξ.le hez hem hec
  refine ⟨F,Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [htail,hzero] with Z ht hz
  refine ⟨ht.1,?_⟩
  intro s R seed W hn hm hs hl p hp₁ hp₂ beta M a reserve padding t hZ hbeta hM hMB ha haB
    hreserve hω hvol hamp hpadding hseed hseed0 hsource hcap hA hpool reflected key
    hK A rows C source radius Fourier weight scalar
  have hzt := hz.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ beta M a reserve padding t hZ
    hbeta hM hvol hamp (abs_le.mp hA).2 hpadding hseed hseed0 hsource hcap hpool reflected key
  have htt := ht.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ M a reserve t hZ
    hM hMB ha haB hreserve hω hseed hseed0 hsource hcap hA hpool reflected key
  have hh := actual_geometry_main_second_split reflected s R seed (Z^M) Z ξ M A
    (3*a) reserve b t N hK (zero_lt_one.trans hZ) key weight
    (fun q=>Fourier q.1)
  simp only [Fintype.sum_sigma,mul_add,Finset.sum_add_distrib] at hh
  apply hh.trans
  refine add_le_add ?_ ?_
  · trace "ADD_APPLIED"
    apply add_le_add
    · simpa only [geometryHighFactor,one_div] using hzt
    · exact htt
  · exact le_refl _

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_main_remainder

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_main_zero_with_window
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Filter CenteredMomentSectorLocalization

/-- The common loss unit precedes the slot dictionary and all density degrees. -/
def geometryLossUnit (Mmin εaffine : ℝ) : ℝ :=
  min (εaffine/128) (min ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))

theorem geometry_loss_unit_pos (Mmin εaffine : ℝ) (hM : 0<Mmin) (hε : 0<εaffine) :
    0<geometryLossUnit Mmin εaffine := by unfold geometryLossUnit;positivity

/-- Sixty-four units fit inside half the smallest physical reserve. -/
theorem geometry_loss_unit_reserve (Mmin εaffine M : ℝ) (hM : Mmin≤M) :
    128*geometryLossUnit Mmin εaffine≤εaffine ∧
      64*geometryLossUnit Mmin εaffine≤M*(7/60000000) := by
  have h₁ := min_le_left (εaffine/128) (min ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))
  have h₂ := (min_le_right (εaffine/128) _).trans
    (min_le_left ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))
  change geometryLossUnit Mmin εaffine≤_ at h₁ h₂
  constructor <;> linarith

/-- Every larger branch reserve can use the same loss unit. The actual
branch estimates must supply their own total loss bound. -/
theorem geometry_paid_loss (Mmin εaffine M reserve loss : ℝ)
    (hMmin : 0<Mmin)(hM : Mmin≤M)(hr : (7/30000000:ℝ)≤reserve)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    -M*reserve+loss≤-M*(7/60000000) := by
  have hb := (geometry_loss_unit_reserve Mmin εaffine M hM).2
  have hMr := mul_le_mul_of_nonneg_left hr (hMmin.trans_le hM).le
  linarith

theorem geometry_high_reserve_ge_low :
    (7/30000000:ℝ)≤720486667/30493190000000 := by norm_num

/-- The fixed localization constant is absorbed before sources move. -/
theorem eventual_geometry_small_frequency (μ : ℝ)(hμ : 0<μ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (μ/64)+μ/8 ∧
      frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128 := by
  filter_upwards [(tendsto_rpow_atTop (by positivity : 0<μ/8)).eventually
    (eventually_ge_atTop (128:ℝ)),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  have hlog : Real.logb Z 128≤μ/8 :=
    (Real.logb_le_iff_le_rpow hZ (by norm_num : (0:ℝ)<128)).mpr hz
  have hfreq := frequencyLoss_nonneg Z 32 (μ/64) hZ (by norm_num) (by positivity)
  refine ⟨hZ,by positivity,?_⟩
  dsimp only [frequencyLoss]
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith

/-- Width and padding choices are independent of the slot count. -/
theorem geometry_width_padding_budget (μ Mmax M omega : ℝ)
    (hμ : 0<μ)(hmax : 0≤Mmax)(hM : M≤Mmax)(hω : omega≤33*μ/128) :
    μ/(4*(Mmax+1))*M+μ/128≤33*μ/128 ∧
      omega+μ/(4*(Mmax+1))*M≤3*μ/4 := by
  have hp : 0<4*(Mmax+1) := by positivity
  have he := div_mul_cancel₀ μ (ne_of_gt hp)
  have hratio : 0<μ/(4*(Mmax+1)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hM hratio.le
  have hb : μ/(4*(Mmax+1))*M≤μ/4 := by nlinarith
  constructor <;> linarith

/-- These losses are selected after the fixed slot count is known. Their
products with the count and the source caps still have fixed small budgets. -/
theorem geometry_dictionary_loss_budgets (μ d B : ℝ)(N : ℕ)
    (hμ : 0<μ)(hd : 0≤d)(hB : 0≤B) :
    let εplain := μ/(64*(d+1))
    let εslot := μ/(64*(d+1)*(N+1))
    let εerror := μ/(8*(N+1))
    let εmass := μ/(8*(B+1))
    0<εplain ∧ 0<εslot ∧ 0<εerror ∧ 0<εmass ∧
      2*d*εplain≤μ/32 ∧ 2*d*N*εslot≤μ/32 ∧
      (N:ℝ)*εerror≤μ/8 ∧ B*εmass≤μ/8 ∧
      μ/16+2*d*εplain+2*d*N*εslot≤μ/4 := by
  intro εplain εslot εerror εmass
  have hp : 0<εplain := by dsimp [εplain];positivity
  have hs : 0<εslot := by dsimp [εslot];positivity
  have he : 0<εerror := by dsimp [εerror];positivity
  have hm : 0<εmass := by dsimp [εmass];positivity
  have ep : εplain*(64*(d+1))=μ := div_mul_cancel₀ _ (by positivity)
  have es : εslot*(64*(d+1)*(N+1))=μ := div_mul_cancel₀ _ (by positivity)
  have ee : εerror*(8*(N+1))=μ := div_mul_cancel₀ _ (by positivity)
  have em : εmass*(8*(B+1))=μ := div_mul_cancel₀ _ (by positivity)
  have hN : (0:ℝ)≤N := Nat.cast_nonneg _
  have hp' : 2*d*εplain≤μ/32 := by nlinarith
  have hs' : 2*d*N*εslot≤μ/32 := by
    nlinarith [mul_nonneg hd hs.le,mul_nonneg hN hs.le]
  refine ⟨hp,hs,he,hm,hp',hs',?_,?_,?_⟩ <;> nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_loss_unit_pos
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_loss_unit_reserve
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_paid_loss
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_high_reserve_ge_low
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_geometry_small_frequency
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_width_padding_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_dictionary_loss_budgets
end
