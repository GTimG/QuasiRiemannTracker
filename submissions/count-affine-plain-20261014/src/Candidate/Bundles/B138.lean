/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B064
import Candidate.Bundles.B080
import Candidate.Bundles.B087
import Candidate.Bundles.B090
import Candidate.Bundles.B109
import Candidate.Bundles.B136
import Candidate.Bundles.B137
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalZeroRadius

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainRemainder; sha256 35a1cea60fc10c3ba5fc78f7f432f7bf67733719a084a956790a8cd7d61b0c88 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                    
                                                       
                                                       

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
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
    (hCs : 1≤ Cs) (hbs : 1≤ bs) (hlo : 0< lo) (hhi : 0≤ hi) (hslotlo : 0< slotlo)
    (hAmax : 0≤ Amax) (hB : 0≤ B) (hU : 0≤ U) (hξ : 0≤ξ)
    (hez : 0<εzero) (hem : 0<εmass) (hec : 0<εcount) :
    ∃Czero : ℝ, 0< Czero ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤ N → (∀j,s.M j≤ Cs) → s.upper≤ bs → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1< Z),
      3401/100000≤ beta ∧ beta≤1/25 → 0≤ M →
      (Real.logb Z (volume s))≤ M*Cycle61.Arithmetic.totalA beta →
      a≤ M*Cycle61.Arithmetic.amp beta → (Real.logb Z (volume s))≤ Amax →
      bs^N≤ Z^padding → Squarefree seed → seed≠0 →
      0< sourceRadius s → sourceRadius s≤ Z^B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
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
  have hs₁ : ∀x,s.W₁ x≠0→ lo≤ x := by
    intro x hx; rw [hp₁] at hx; exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→ lo≤ x := by
    intro x hx; rw [hp₂] at hx; exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos s)).symm
  have hVcap : volume s≤ Z^Amax := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hZ.le hA'
  have hKi : (Z^M)⁻¹≤ Z^(0:ℝ) := by
    rw [Real.rpow_zero]
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow hZ.le hM
  have hrows : rows⊆firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus) :=
    Finset.Subset.refl _
  have hprojector : ∀r∈rows,(r.2.1.val.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
    intro r hr
    exact actual_geometry_projector_cap s N R seed (Z^M) Z ξ U hK hn hZ.le hU hpool key r
  have hzero := hfamily s hn hm hs p hp₁ hp₂ Φ reflected R seed Z beta M A a ξ reserve padding
    hZ hb hM hA ha hV hgeo key weight rows t
  have hmass := hz.2 s R seed W M a reserve padding εzero εmass hZ hn hl hez.le hem.le
    hseed hseed0 hz₁ hz₂ hsource hcap hVcap hKi hs₁ hs₂ reflected key rows hrows hprojector
  apply hzero.trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤ K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖)).trans_eq
  ring


/-- The actual amplified main source is reduced to its single joint retained
sum. The full zero and discarded contributions are paid uniformly from the
original profiles, with the physical-D and seed factors preserved. -/
theorem eventual_actual_geometry_main_remainder {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εzero εmass εcount saving : ℝ)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hlo : 0< lo)(hhi : 0≤ hi)(hslotlo : 0< slotlo)
    (hB : 0≤ B)(hU : 0≤ U)(hξ : 0<ξ)(hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Czero Ctail : ℝ,0< Czero ∧ 0< Ctail ∧
    ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤ N → (∀j,s.M j≤ Cs) → s.upper≤ b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1< Z),
      3401/100000≤ beta ∧ beta≤1/25 →
      0≤ M → M≤ B → 0≤ a → a≤ B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤ B →
      Real.logb Z (volume s)≤ M*Cycle61.Arithmetic.totalA beta →
      a≤ M*Cycle61.Arithmetic.amp beta → b^N≤ Z^padding →
      Squarefree seed → seed≠0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_remainder

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_zero_with_window

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainRemainder -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLossSchedule; sha256 8b62a89a92e77099a6635615c93eeb42ed7f55c74dc88d64d2d9370f024f53ae -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                       
                                                         
                                    

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open Filter CenteredMomentSectorLocalization

/-- The common loss unit precedes the slot dictionary and all density degrees. -/
def geometryLossUnit (Mmin εaffine : ℝ) : ℝ :=
  min (εaffine/128) (min ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))

theorem geometry_loss_unit_pos (Mmin εaffine : ℝ) (hM : 0< Mmin) (hε : 0<εaffine) :
    0< geometryLossUnit Mmin εaffine := by unfold geometryLossUnit;positivity

/-- Sixty-four units fit inside half the smallest physical reserve. -/
theorem geometry_loss_unit_reserve (Mmin εaffine M : ℝ) (hM : Mmin≤ M) :
    128*geometryLossUnit Mmin εaffine≤εaffine ∧
      64*geometryLossUnit Mmin εaffine≤ M*(7/60000000) := by
  have h₁ := min_le_left (εaffine/128) (min ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))
  have h₂ := (min_le_right (εaffine/128) _).trans
    (min_le_left ((7/30000000)*Mmin/128) (min (Mmin/128) (1/128)))
  change geometryLossUnit Mmin εaffine≤ _ at h₁ h₂
  constructor <;> linarith

/-- Every larger branch reserve can use the same loss unit. The actual
branch estimates must supply their own total loss bound. -/
theorem geometry_paid_loss (Mmin εaffine M reserve loss : ℝ)
    (hMmin : 0< Mmin)(hM : Mmin≤ M)(hr : (1/3750000:ℝ)≤ reserve)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    -M*reserve+loss≤-M*(7/60000000) := by
  have hb := (geometry_loss_unit_reserve Mmin εaffine M hM).2
  have hMr := mul_le_mul_of_nonneg_left hr (hMmin.trans_le hM).le
  linarith

theorem geometry_high_reserve_ge_low :
    (1/3750000:ℝ)≤781136071/45083880000000 := by norm_num

/-- The fixed localization constant is absorbed before sources move. -/
theorem eventual_geometry_small_frequency (μ : ℝ)(hμ : 0<μ) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧
      0≤ frequencyLoss Z 32 (μ/64)+μ/8 ∧
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
    (hμ : 0<μ)(hmax : 0≤ Mmax)(hM : M≤ Mmax)(hω : omega≤33*μ/128) :
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
    (hμ : 0<μ)(hd : 0≤ d)(hB : 0≤ B) :
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
  have hN : (0:ℝ)≤ N := Nat.cast_nonneg _
  have hp' : 2*d*εplain≤μ/32 := by nlinarith
  have hs' : 2*d*N*εslot≤μ/32 := by
    nlinarith [mul_nonneg hd hs.le,mul_nonneg hN hs.le]
  refine ⟨hp,hs,he,hm,hp',hs',?_,?_,?_⟩ <;> nlinarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_loss_unit_pos
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_loss_unit_reserve
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_paid_loss
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_high_reserve_ge_low
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_small_frequency
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_width_padding_budget
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_dictionary_loss_budgets

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLossSchedule -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMeshChoice; sha256 06413710d6f635d1ab3a4bb9347f90e6585c6b659e3051c887136769f085b143 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                        
                                                        
                                                     
                                        

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimePool CenteredMomentAmplificationSlotGap CenteredMomentAmplificationEligibility
open CenteredMomentPrimeElements CompletedGauss
local notation "O" => HeckeFamily.O

/-- The analytic mesh is fixed before a chosen slot dictionary or its size. -/
def geometryAnalyticMesh (Mmin Mmax εaffine Mcap Bmask L : ℝ) : ℝ :=
  let μ:=geometryLossUnit Mmin εaffine
  min (Cycle61FirstActual.comparisonMesh Mmin Mmax εaffine)
    (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*(62485051/9854400000)/4)))/2

theorem geometry_analytic_mesh_admission (Mmin Mmax εaffine Mcap Bmask L : ℝ)
    (hmin : 0< Mmin)(hmax : Mmin≤ Mmax)(hε : 0<εaffine)
    (hcap : 0< Mcap)(hmask : 0≤ Bmask) :
    let μ:=geometryLossUnit Mmin εaffine
    let mesh:=geometryAnalyticMesh Mmin Mmax εaffine Mcap Bmask L
    0< mesh ∧ mesh≤ Cycle61FirstActual.comparisonMesh Mmin Mmax εaffine ∧
      mesh≤ Cycle25.Energy.commonMesh Mcap Bmask L (μ/8) ∧ mesh≤μ/8 ∧
      mesh< Mmin*(62485051/9854400000)/2 := by
  intro μ mesh
  have hu : 0<μ := geometry_loss_unit_pos Mmin εaffine hmin hε
  have hc := Cycle61FirstActual.comparisonMesh_pos Mmin Mmax εaffine hmin hmax hε
  have ho := Cycle25.Energy.commonMesh_pos Mcap Bmask L (μ/8) hcap.le hmask (by positivity)
  have hm : 0< mesh := by dsimp [mesh,geometryAnalyticMesh];change 0< min _ (min _ (min (μ/8) _))/2;positivity
  have ha : 2*mesh≤ Cycle61FirstActual.comparisonMesh Mmin Mmax εaffine := by
    dsimp [mesh,geometryAnalyticMesh];linarith [min_le_left
      (Cycle61FirstActual.comparisonMesh Mmin Mmax εaffine)
      (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8)) (min (μ/8) (Mmin*(62485051/9854400000)/4)))]
  have ht : 2*mesh≤ min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*(62485051/9854400000)/4)) := by
    dsimp [mesh,geometryAnalyticMesh];linarith [min_le_right
      (Cycle61FirstActual.comparisonMesh Mmin Mmax εaffine)
      (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8)) (min (μ/8) (Mmin*(62485051/9854400000)/4)))]
  have hb := ht.trans (min_le_left _ _)
  have hd := ht.trans (min_le_right _ _)
  have he := hd.trans (min_le_left _ _)
  have hf := hd.trans (min_le_right _ _)
  refine ⟨hm,?_,?_,?_,?_⟩ <;> linarith

variable (rayM : Ideal O) [NeZero rayM]
local instance meshFiniteQuotient : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤ H)

/-- The actual annular amplifier pool is disjoint from every original
stored slot, uniformly before sources and supported cell widths move. -/
theorem eventual_actual_amplifier_slot_coprime (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad)
    (Mmin mesh bslot : ℝ)(hmin : 0< Mmin)
    (hmesh : mesh< Mmin*(62485051/9854400000)/2) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧
    ∀{α : Type*}[Fintype α][DecidableEq α],
    ∀(s : Input α)(η₀ : Character)(θ : α→ RayQuotient.Characters rayM H)
      (w σ v : α→ℝ)(W : ℝ→ℂ),
      Matches rayM H hH s η₀ θ w σ v W bslot Z → (∀j,w j≤ mesh) →
    ∀M beta : ℝ,Mmin≤ M → 3401/100000≤ beta → beta≤1/25 →
    ∀Q∈primePool rayM H Sbad (1/2) 1 (Z^(M*Cycle61.Arithmetic.amp beta)),
      ∀j I,I∈s.slots j→ IsCoprime Q I := by
  let ell:=Mmin*(62485051/9854400000)/2
  filter_upwards [eventually_scale_gap (max 1 bslot) mesh ell hmesh,
    Cycle61.Physical.actual_amplifier_prime_width rayM H Sbad Mmin hmin] with Z hg hp
  refine ⟨hp.1,?_⟩
  intro α _ _ s η₀ θ w σ v W hm hw M beta hM hb₁ hb₂ Q hQ
  have hd := primePool_data rayM H Sbad hbad (1/2) 1 (Z^(M*Cycle61.Arithmetic.amp beta)) Q hQ
  have hn := (hp.2 M beta hM hb₁ hb₂ Q hQ).1
  have ha := (Cycle61.Arithmetic.amp_bounds ⟨hb₁,hb₂⟩).1
  have hm0 : 0≤ M := (hmin.trans_le hM).le
  have hprod := mul_le_mul_of_nonneg_left ha hm0
  have hell : ell≤3*(M*Cycle61.Arithmetic.amp beta)/4 := by dsimp [ell];nlinarith
  have hnorm : 0<(Q.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos Q hd.1.ne_zero
  have hQN : Z^ell≤(Q.absNorm:ℝ) :=
    (Real.le_logb_iff_rpow_le hp.1 hnorm).mp (hell.trans hn)
  exact actual_full_slot_coprime rayM H hH s η₀ θ w σ v W bslot Z mesh ell hp.1.le hm hw Q hd.1 hQN hg.2

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_analytic_mesh_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_amplifier_slot_coprime

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMeshChoice -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineAssembly; sha256 e07fd7be7caa52828d2ad65a36bf238500245a419f0f24482a6a9f163a952f17 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                      
                                                      
                                     
                                     
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentLogDyadic Cycle61InitialSource Cycle61Physical Cycle61Moment
open CenteredMomentFirstSourceReduction CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- Constants are collected over every subset of the fixed original slot type,
before any live source, geometry bin, or shifted Mellin height is chosen. -/
theorem uniform_geometry_mass {α : Type*} [Fintype α] [DecidableEq α]
    (Ψ : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ) (ξ εbin : ℝ)
    (hξ : 0≤ξ) (hεbin : 0<εbin)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
    ∀T : Finset α,∀s : Input T,∀N : ℕ,∀a b E : ℝ,
      0< a → Fintype.card T≤ N → a≤ s.lower → s.upper≤ b →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^(3:ℝ) → volume s≤ Z^(2:ℝ) → 0≤ E →
    ∀H : ℤ×(Fin 5→ℤ)→ℝ,
      (∀key∈commonGeometryBins s 1 1 Z Z ξ,0< H key) →
      (∀key∈commonGeometryBins s 1 1 Z Z ξ,∀(reflected : Bool)(t u : ℝ),
        geometryLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
          (zero_lt_one.trans hZ) key
          (fun q=>normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q)) N b
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
          ((if reflected then E/H key else E*H key)*(1+‖t‖)^degree)*
            (1+‖u‖)^(2*windowDegree)) →
      physicalMass s 1 1 fixedBadMask 1 Ψ Z Z ξ/volume s≤ C*E*Z^(1+εbin) := by
  have hm (T : Finset α) := actual_physical_mass_from_geometry_budgets (ι:=T)
    Ψ 0 degree windowDegree hc hsm
  choose Cm hCm hm using hm
  have hb (T : Finset α) := common_geometry_bins_subpower (ι:=T) 2 2 3 ξ εbin
    (by norm_num) (by norm_num) (by norm_num) hξ hεbin
  choose Cb hCb hb using hb
  let C := 1+∑T : Finset α,Cm T*Cb T
  have ht (T : Finset α) : 0≤ Cm T*Cb T := mul_nonneg (hCm T) (hCb T).le
  have hC : 0< C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=>ht T)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_all.mpr hb,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro _hZ T s N a b E ha hn hlo hhi hz₁ hz₂ hr hV hE H hH hbudget
  have hCt : Cm T*Cb T≤ C := by
    have hh := Finset.single_le_sum (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=>ht T)
      (Finset.mem_univ T)
    dsimp [C];linarith
  by_cases hsource : 0< sourceRadius s
  · have hKi : Z⁻¹≤ Z^(2:ℝ) := (inv_le_one_of_one_le₀ hZ.le).trans
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤2))
    have hcard := hb T s 1 1 Z (zero_lt_one.trans hZ) (by simp) hz₁ hz₂ hsource hr hV hKi
    have hh := hm T s 1 1 Z Z ξ 3 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) hZ N a b ha hn hlo hhi (by simp) hz₁ hz₂ hr
      (fun _=>E) H (fun _ _=>hE) hH hbudget
    have hs : (∑key∈commonGeometryBins s 1 1 Z Z ξ,
        E/(1+dyadicScale key.1)^(0:ℕ))=
        ((commonGeometryBins s 1 1 Z Z ξ).card:ℝ)*E := by simp
    rw [hs,CenteredMomentFirstPhysicalOriginalMask.original_physicalMass] at hh
    have hv := volume_pos s
    apply (div_le_iff₀ hv).mpr
    calc
      physicalMass s 1 1 fixedBadMask 1 Ψ Z Z ξ
          ≤ Cm T*Z^(1:ℝ)*volume s*((commonGeometryBins s 1 1 Z Z ξ).card:ℝ)*E := by
            exact hh.trans_eq (by ring)
      _ ≤ Cm T*Z^(1:ℝ)*volume s*(Cb T*Z^εbin)*E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard
          (mul_nonneg (mul_nonneg (hCm T) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hv.le)) hE
      _ = (Cm T*Cb T)*E*Z^(1+εbin)*volume s := by
        rw [Real.rpow_add (zero_lt_one.trans hZ)];ring
      _ ≤ C*E*Z^(1+εbin)*volume s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt hE)
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hv.le
  · rw [CenteredMomentFirstPhysicalZeroRadius.physicalMass_zero s 1 1 hz₁ hz₂
      (le_of_not_gt hsource) fixedBadMask 1 Ψ Z Z ξ]
    simp only [zero_div]
    exact mul_nonneg (mul_nonneg hC.le hE) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)


variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineAssemblyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ)(hHray : RayOrthogonality.globalUnits rayM≤ Hray)

/-- The pending input is the literal full live budget, including the actual
phase weight and both orientations at every first-Mellin shifted height.
There is no initial energy or physical-mass premise. -/
def LiteralAffineGeometryBudget
    (W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εmass τ ξ : ℝ) : Prop :=
  ∀Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
    (∀x,0≤(Ψ x).re) →
  ∃externalDegree outerDegree windowDegree : ℕ,∃S : Finset (ℕ×ℕ),
  ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
  ∀T : Finset α,∀θ : T→ RayQuotient.Characters rayM Hray,
  ∀w σ freq : T→ℝ,∀t height : ℝ,
    (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    ∀hσlo : (∀i,(33/50:ℝ)≤σ i),∀hσhi : (∀i,σ i≤(33/50:ℝ)),
    0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
  ∀Φ : 𝓢(ℝ,ℂ),∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
  ∀hpΦ : ∀x,0≤(Φ x).re,∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,
  ∀hX₁ : 0< X₁,∀hX₂ : 0< X₂,
    (41/100:ℝ)≤ length Z X₁ → length Z X₁≤(44/100:ℝ) →
    (41/100:ℝ)≤ length Z X₂ → length Z X₂≤(44/100:ℝ) →
    (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
    length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B →
  let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ;
  let inp:=affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
    1 t X₁ X₂ hX₁ hX₂;
  let E:=C*(p.control S)^2*(1+|t|+height)^externalDegree*Z^εmass;
  ∃H : ℤ×(Fin 5→ℤ)→ℝ,
    (∀key∈commonGeometryBins inp 1 1 Z Z ξ,0< H key) ∧
    ∀key∈commonGeometryBins inp 1 1 Z Z ξ,∀(reflected : Bool)(t' u : ℝ),
      geometryLiveBudget reflected inp 1 1 Z Z ξ 1 (Real.logb Z (volume inp))
        (zero_lt_one.trans hZ) key
        (fun q=>normPhase (coordinateBlock inp 1 1 Ψ Z Z ξ q)) (Fintype.card α) (9/4)
        (inp.t+2*Real.pi*(u-(if reflected then -t' else t')))≤
        ((if reflected then E/H key else E*H key)*(1+‖t'‖)^outerDegree)*
          (1+‖u‖)^(2*windowDegree)

/-- End-to-end width-one assembly for one fixed chosen character and ideal.
Only the actual live-budget estimate is pending. -/
theorem literal_geometry_initial_affine
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh ε τ ξ : ℝ)
    (hbΦ : 0< bΦ)(hmesh : 0< mesh)(hε : 0<ε)(hτ : 0<τ)(hξ : 0<ξ)
    (hmeshComparison : mesh≤ Cycle61FirstActual.comparisonMesh 1 1 (ε/2))
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (hQray : Q≤ rayM)(hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (hbudget : LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW.continuous
      hWs η η₀ Q bΦ mesh (ε/4) τ ξ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      InitialAffineAt (α:=α) rayM Hray hHray W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε Z η η₀ Q degree S C := by
  let anchors : Fin 1→ Character:=fun _=>η
  obtain ⟨Ψ,hΨ,hΨpos,_,jr,Sr,hred⟩ := actual_initial_source_reduction_fixed_mesh
    (α:=α) rayM Hray hHray anchors W 1 2 (33/50) (33/50) (1/4) (9/4) bΦ
    1 1 (ε/2) ξ (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) (by positivity) hξ hbeta hκbeta
  obtain ⟨Cr,hCr,hred⟩:=hred η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨jb,jo,jw,Sb,Cb,hCb,hbud⟩:=hbudget Ψ hΨ hΨpos
  obtain ⟨Cm,hCm,hmass⟩:=uniform_geometry_mass (α:=α) Ψ jo jw ξ (ε/4) hξ.le
    (by positivity) hc hsm
  let Js:=max jr jb
  let Ss:=Sr∪Sb
  let Cs:=2*Cm*Cb+Cr
  have hCs : 0< Cs := by dsimp [Cs];positivity
  have hsmall : ∀ᶠ Z : ℝ in atTop,
      BoundedInitialAffineAt (α:=α) rayM Hray hHray W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε τ Z η η₀ Q Js Ss Cs := by
    obtain hcaps := eventual_affine_polynomial_caps (α:=α) rayM Hray hHray W hW.continuous
      1 2 (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [hred,hbud,hmass,hcaps,eventually_gt_atTop (1:ℝ)] with Z hr hb hm hcaps hZ
    intro T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight M hM₁ hM₂ Φ hsΦ hpΦ
      p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslotlo hslothi hcell
    have hM : M=1 := le_antisymm hM₂ hM₁
    subst M
    simp only [mul_one] at hlo₁ hhi₁ hlo₂ hhi₂ hslotlo hslothi hcell
    let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
    let inp:=affineInput rayM Hray hHray η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
      1 t X₁ X₂ hX₁ hX₂
    have hN : Fintype.card T≤ Fintype.card α :=
      Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
    have hcap:=hcaps.2 T η₀ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state p
      1 t X₁ X₂ hX₁ hX₂ (by norm_num) (by norm_num) hw (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)
      (by simpa only [mul_one] using hhi₁) (by simpa only [mul_one] using hhi₂) hslothi
    obtain ⟨H,hH,hbound⟩:=hb hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight
      Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslotlo hslothi hcell
    have he : 0≤ Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(ε/4) := by positivity
    have hz₁ : inp.W₁ 0=0 := CenteredMomentDetectorPlainSource.support_zero
      (p.profile 0) (1/4) (9/4) (by norm_num) (p.support 0)
    have hz₂ : inp.W₂ 0=0 := CenteredMomentDetectorPlainSource.support_zero
      (p.profile 1) (1/4) (9/4) (by norm_num) (p.support 1)
    have hm' := hm hZ T inp (Fintype.card α) (1/4) (9/4)
      (Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(ε/4)) (by norm_num) hN
      (by change (1/4:ℝ)≤1;norm_num) (by change (2:ℝ)≤9/4;norm_num)
      hz₁ hz₂
      (by simpa only [show (1:ℝ)+2=3 by norm_num] using hcap.2.2.2.1)
      (by simpa only [show (1:ℝ)+1=2 by norm_num] using hcap.2.2.1) he H hH hbound
    have hr' := hr.2 (0:Fin 1) T θ w σ freq t height hw
      (fun i=>(hwm i).trans hmeshComparison) hσlo hσhi hh hv
      1 (by norm_num) (by norm_num) Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hhi₁)
      (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₂)
      hslothi hZ (by norm_num)
    have hpcR := profile_control_mono p (Finset.subset_union_left (s₁ := Sr) (s₂ := Sb))
    have hpcB0 := p.control_nonneg Sb
    have hpcB := profile_control_mono p (Finset.subset_union_right (s₁ := Sr) (s₂ := Sb))
    have hbase : 1≤1+|t|+height := by linarith [abs_nonneg t]
    have hpowR : (1+|t|+height)^jr≤(1+|t|+height)^Js :=
      pow_le_pow_right₀ hbase (le_max_left jr jb)
    have hpowB : (1+|t|+height)^jb≤(1+|t|+height)^Js :=
      pow_le_pow_right₀ hbase (le_max_right jr jb)
    have hzpow : Z^(1+ε/2)≤ Z^(1+ε) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hm'' : physicalMass inp 1 1 fixedBadMask 1 Ψ Z Z ξ/volume inp≤
        Cm*Cb*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε) := by
      apply hm'.trans
      calc
        _ = Cm*Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(1+ε/2) := by
          calc
            _ = Cm*Cb*(p.control Sb)^2*(1+|t|+height)^jb*
                (Z^(ε/4)*Z^(1+ε/4)) := by ring
            _ = _ := by
              rw [←Real.rpow_add (zero_lt_one.trans hZ)]
              have heq : ε/4+(1+ε/4)=(1:ℝ)+ε/2 := by ring
              rw [heq]
        _ ≤ _ := by dsimp [Ss];gcongr
    change initialEnergy rayM Hray hHray W 2 Z 1 η η₀ Q T θ w σ freq t X₁ X₂
      (p.profile 0) (p.profile 1) Φ≤ _
    change initialEnergy rayM Hray hHray W 2 Z 1 η η₀ Q T θ w σ freq t X₁ X₂
      (p.profile 0) (p.profile 1) Φ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^(1:ℝ)) Z ξ/volume inp)+
      Cr*diagonalControl Φ*(p.control Sr)^2*(1+|t|+height)^jr*Z^(1+ε/2) at hr'
    apply hr'.trans
    have hd := diagonalControl_nonneg Φ
    have hpc0:=p.control_nonneg Sr
    calc
      _ ≤ 2*diagonalControl Φ*(Cm*Cb*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε))+
          Cr*diagonalControl Φ*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε) := by
        apply add_le_add
        · simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left hm'' (mul_nonneg (by norm_num) hd)
        · dsimp only [Ss]
          gcongr
      _ = _ := by dsimp [Cs];ring
  obtain ⟨jc,Sc,hcoarse⟩:=original_initial_coarse (α:=α) rayM Hray hHray W 1 2
    (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 1 (by norm_num) hWs hW
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ hmesh.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbeta anchors
  obtain ⟨Cc,hCc,hcoarse⟩:=hcoarse η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,hext⟩:=initial_height_extend (α := α) (Label := Fin 1) rayM Hray hHray W 2
    (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (1+2*(Fintype.card α:ℝ)*mesh) ε τ hτ (by norm_num) (by norm_num) Js jc Ss Sc
  refine ⟨degree,Ss∪Sc,Cs+Cc,add_pos hCs hCc,?_⟩
  have hh:=hext anchors η₀ Q Cs Cc hCs.le hCc.le
    (hsmall.mono (fun _ h _=>h)) (hcoarse.mono (fun _ h=>h.2))
  exact hh.mono (fun _ h=>h (0:Fin 1))


open Cycle25WeightedNumeratorPhysical CenteredMomentDetectorDictionary ProbePhysical

/-- Chosen reflected numerator source: all original masks and fixed exclusions
are retained, while the pending estimate remains a literal live budget. -/
def SourceLiteralAffineGeometryBudget {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh εmass τ ξ : ℝ) : Prop :=
  let W:=fun x=>conj (F.W x)
  let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
  let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
  let η:=fixedSourcePrincipal F.S F.exclusions.prime
  LiteralAffineGeometryBudget (α:=Fin D.N) F.modulus ⊤ le_top W hW hs
    η η (weighted_sourceFixedIdeal F) bΦ mesh εmass τ ξ

/-- The exact public fourth-moment input follows from the genuine full
geometry budget. Constants precede every live row, profile and height. -/
theorem weighted_source_affine_from_geometry {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε τ ξ : ℝ)(hbΦ : 0< bΦ)(hmesh : 0< mesh)(hε : 0<ε)
    (hτ : 0<τ)(hξ : 0<ξ)
    (hmeshComparison : mesh≤ Cycle61FirstActual.comparisonMesh 1 1 (ε/2))
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (hbudget : SourceLiteralAffineGeometryBudget F bΦ mesh (ε/4) τ ξ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠ U : ℝ in atTop,
      Cycle61.Numerator.Fourth.AffineAt F bΦ mesh ε U degree S C := by
  let W:=fun x=>conj (F.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
  let η:=fixedSourcePrincipal F.S F.exclusions.prime
  exact literal_geometry_initial_affine (α:=Fin D.N) F.modulus ⊤ le_top W hW hs
    η η (weighted_sourceFixedIdeal F) bΦ mesh ε τ ξ hbΦ hmesh hε hτ hξ
    hmeshComparison hbeta hκbeta (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_geometry_mass
#print axioms OAI.SevenEighths.Cycle61InitialMass.literal_geometry_initial_affine

#print axioms OAI.SevenEighths.Cycle61InitialMass.weighted_source_affine_from_geometry

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineAssembly -/
