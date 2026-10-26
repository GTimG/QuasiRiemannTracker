/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryCellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainTail
import Candidate.Uneven.AuxiliaryZeroPayment
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondSplit

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.AuxiliaryReconstruction
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
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
    (hCs : 1≤Cs) (hbs : 1≤bs) (hlo : 0<lo) (hhi : 0≤hi) (hslotlo : 0< slotlo)
    (hAmax : 0≤Amax) (hB : 0≤B) (hU : 0≤U) (hξ : 0≤ξ)
    (hez : 0<εzero) (hem : 0<εmass) (hec : 0<εcount) :
    ∃Czero : ℝ, 0<Czero ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → s.upper≤bs → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1<Z),
      Sil.Uneven.AuxiliarySource.widthLo≤beta ∧ beta≤Sil.Uneven.AuxiliarySource.widthHi → 0≤M →
      (Real.logb Z (volume s))≤M*Sil.Uneven.AuxiliarySource.total beta →
      a≤M*Sil.Uneven.AuxiliarySource.amp beta → (Real.logb Z (volume s))≤Amax →
      bs^N≤Z^padding → Squarefree seed → seed≠0 →
      0< sourceRadius s → sourceRadius s≤Z^B →
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



end
end OAI.SevenEighths.AuxiliaryReconstruction

