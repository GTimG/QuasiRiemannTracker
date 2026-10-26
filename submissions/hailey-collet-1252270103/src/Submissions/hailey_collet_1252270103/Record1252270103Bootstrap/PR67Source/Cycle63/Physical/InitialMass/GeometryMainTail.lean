import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryTailChild
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryTailPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentSupportedTailAggregate CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
local instance mainTailDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The full literal main second tail has arbitrary saving, with the
physical-D factors and original seed intact. All pointwise radius, child
volume, and Fourier admissibility gates are derived from source geometry. -/
theorem eventual_actual_geometry_main_tail {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εmass εcount saving : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hlo : 0<lo)(hhi : 0≤hi)(hslotlo : 0<slotlo)
    (hB : 0≤B)(hU : 0≤U)(hξ : 0<ξ)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Ctail : ℝ,0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → s.upper≤b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a reserve t : ℝ)(hZ : 1<Z),0≤M → M≤B → 0≤a → a≤B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤B → Squarefree seed → seed≠0 →
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
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc/
        volume (source j alloc))*‖secondDiscardedEnergy (source j alloc).η (source j alloc).t
          (original (source j alloc) (R*C j) j.val.2.1.val).columns
          (original (source j alloc) (R*C j) j.val.2.1.val).beta Φ (radius j) (Fourier j) Z ξ‖)≤
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
          Z^(-saving)/(seed.absNorm:ℝ) := by
  let L : ℝ := ((N:ℝ)+2)*U
  let childSaving : ℝ := saving+B*εmass+18*B+L+3*εcount
  obtain ⟨F,Ct,hCt,htail⟩ := actual_common_child_second_tail (α:=ι) N Cs b lo hi (B+1) ξ childSaving
    hCs (zero_le_one.trans hb) hlo hhi (by positivity) hξ
  obtain ⟨Cw,hCw,hpayment⟩ := eventual_actual_geometry_tail_allocation_payment (ι:=ι)
    N Cs b slotlo lo B U ξ εmass εcount hCs hslotlo hlo hB hU hξ.le hem hec
  refine ⟨F,Ct*Cw,mul_pos hCt hCw,?_⟩
  filter_upwards [htail,hpayment,eventually_ge_atTop (b^(2*N)),eventually_gt_atTop (1:ℝ)]
    with Z ht hw hbZ hZone
  refine ⟨hZone,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ M a reserve t hZ hM hMB ha haB hreserve hω
    hseed hseed0 hsource hcap hA hpool reflected key hK A rows C source radius Fourier weight
  have hs₁ : ∀x,s.W₁ x≠0→lo≤x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→lo≤x := by
    intro x hx;rw [hp₂] at hx;exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  have hV : volume s≤Z^B := (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hbNZ : b^N≤Z := (pow_le_pow_right₀ hb (by omega : N≤2*N)).trans hbZ
  have hvolume (j : rows)(alloc : actualAllocations s.pools (C j))
      (hne : frozenCoefficient alloc.val (C j) R s.ν s.W s.P≠0) : volume (source j alloc)≤Z^(B+1) := by
    have hh := common_volume_le N b hb s hn hs (C j) R alloc
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t hne
    have hnorm : (1:ℝ)≤(C j).absNorm := norm_ge_one _ (allocation_ne s (C j) alloc)
    apply hh.trans
    calc (b^N*volume s)/(C j).absNorm≤b^N*volume s := div_le_self (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le) hnorm
         _≤Z*Z^B := mul_le_mul hbNZ hV (volume_pos s).le (by positivity)
         _=Z^(B+1) := by rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one];ring
  have hFourier (j : rows) : Fourier j≤Z^(B+1) := by
    let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1
    have hh := main_fourier_scale_upper reflected src.C src.D
      (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P:CommonIndex src.C src.D=>P.val) src.inactive})
      src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1 src.sameSupport
      (Z^M) (volume s) Z (3*a) (frequencyLoss Z 32 ξ) reserve b N
      hK (volume_pos s) hZ (zero_lt_one.trans_le hb) (by positivity)
      (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le) hreserve
    change Fourier j≤b^(2*N)*Z^M at hh
    apply hh.trans
    calc b^(2*N)*Z^M≤Z*Z^B := mul_le_mul hbZ
          (Real.rpow_le_rpow_of_exponent_le hZ.le hMB) (by positivity) (by positivity)
         _=Z^(B+1) := by rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one];ring
  let T : ℝ := 12*B-childSaving
  let factor : ℝ := Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hterm (j : rows)(alloc : actualAllocations s.pools (C j)) :
      (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc/
        volume (source j alloc))*‖secondDiscardedEnergy (source j alloc).η (source j alloc).t
          (original (source j alloc) (R*C j) j.val.2.1.val).columns
          (original (source j alloc) (R*C j) j.val.2.1.val).beta Φ (radius j) (Fourier j) Z ξ‖≤
      factor*(geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) := by
    by_cases hne : frozenCoefficient alloc.val (C j) R s.ν s.W s.P≠0
    · have hh := ht.2 s hn hm (fun i=>(s.upper_ge i).trans hs) p hp₁ hp₂
        (C j) R j.val.2.1.val alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ (radius j) (Fourier j)
        (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve (zero_lt_one.trans hZ) _)
        (hvolume j alloc hne) (hFourier j)
        (actual_geometry_main_fourier_admissible reflected s R seed (Z^M) Z ξ (3*a) reserve b N
          hK (zero_lt_one.trans hZ) hb hn hs key j.val alloc t hne)
      have hr := actual_geometry_main_radius_cap reflected s R seed M Z ξ a reserve B hZ hK hB hM
        (abs_le.mp hA).2 haB hω hseed hz₁ hz₂ hcap key j.val
      have hc : ‖secondDiscardedEnergy (source j alloc).η (source j alloc).t
          (original (source j alloc) (R*C j) j.val.2.1.val).columns
          (original (source j alloc) (R*C j) j.val.2.1.val).beta Φ (radius j) (Fourier j) Z ξ‖ /
          volume (source j alloc)≤factor*Z^T := by
        apply hh.trans
        calc factor*(radius j)*Z^(-childSaving)≤factor*Z^(12*B)*Z^(-childSaving) := by gcongr
             _=factor*Z^T := by rw [mul_assoc,←Real.rpow_add (zero_lt_one.trans hZ)];rfl
      rw [div_mul_eq_mul_div,mul_div_assoc]
      apply (mul_le_mul_of_nonneg_left hc (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc)).trans_eq
      ring
    · have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc=0 := by
        simp only [geometryAllocationWeight,C,hne,ite_false]
      rw [hw0,zero_div,zero_mul,zero_mul,mul_zero]
  have hpaid := hw.2 s R seed W M T hZ hn hm hl hseed hseed0 hz₁ hz₂ hsource hcap hA hM
    hs₁ hs₂ hpool reflected key
  have he : B*εmass+T+6*B+((N:ℝ)+2)*U+3*εcount=-saving := by dsimp only [T,childSaving,L];ring
  rw [he] at hpaid
  calc
    _≤∑j : rows,∑alloc : actualAllocations s.pools (C j),
      factor*(geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) :=
      Finset.sum_le_sum (fun j _=>Finset.sum_le_sum (fun alloc _=>hterm j alloc))
    _=factor*(∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) := by
      simp only [Finset.mul_sum]
    _≤factor*_ := mul_le_mul_of_nonneg_left hpaid (by dsimp only [factor];positivity)
    _=_ := by dsimp only [factor];ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
