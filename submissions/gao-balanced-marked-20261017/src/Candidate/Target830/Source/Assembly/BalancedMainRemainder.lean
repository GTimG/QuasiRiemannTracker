import Candidate.Target830.Source.CellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainTail
import Candidate.Target830.Source.Reconstruction.GeometryZeroPayment
import Candidate.Target830.Source.Assembly.BalancedSecondSplit
import Candidate.Target830.Source.Reconstruction.GeometryMainRemainder

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open Cycle63InitialMass Reconstruction
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
variable {plane : SourcePlane}
local instance mainRemainderDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

open EisensteinSchwartzPoisson CenteredMomentSecondLocalization
/-- The actual amplified main source is reduced to its single joint retained
sum. The full zero and discarded contributions are paid uniformly from the
original profiles, with the physical-D and seed factors preserved. -/
theorem eventual_actual_geometry_main_remainder {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εzero εmass εcount saving : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hlo : 0<lo)(hhi : 0≤hi)(hslotlo : 0< slotlo)
    (hB : 0≤B)(hU : 0≤U)(hξ : 0<ξ)(hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → s.upper≤b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t : ℝ)(hZ : 1<Z),
      widthLower≤beta ∧ beta≤widthUpper →
      0≤M → M≤B → 0≤a → a≤B → 0≤reserve →
      frequencyLoss Z 32 ξ+reserve≤B →
      Real.logb Z (volume s)≤M*plane.total beta →
      a≤M*plane.amp beta → b^N≤Z^padding →
      Squarefree seed → seed≠0 →
      0< sourceRadius s → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B →
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
      balancedAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),scalar j alloc*
      actualMainSource (source j alloc) (geometryBranch reflected s R seed (Z^M) Z ξ hK key j.val)
        Z (3*a) 1 ξ reserve)≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier ballProfile 0‖*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(Reconstruction.zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ)+
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
  refine add_le_add ?_ (le_refl _)
  apply add_le_add
  · simp only [geometryHighFactor,one_div] at hzt ⊢
    apply le_trans ?_ hzt
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro alloc _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (volume_pos _).le
    exact actual_balanced_allocation_weight_le reflected s R seed (Z^M) Z ξ M A hK hZ key weight N b j.val alloc
  · apply le_trans ?_ htt
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro alloc _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (volume_pos _).le
    exact actual_balanced_allocation_weight_le reflected s R seed (Z^M) Z ξ M A hK hZ key weight N b j.val alloc

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.eventual_actual_geometry_main_remainder


