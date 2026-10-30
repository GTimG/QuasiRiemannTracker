/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B117
import Candidate.Bundles.B133
import Candidate.Bundles.B135
import Candidate.Bundles.B150
import Candidate.Bundles.B155
import Candidate.Bundles.B161
import Candidate.Bundles.B172
import Candidate.Bundles.B173
import Candidate.Bundles.B174
import Candidate.Bundles.B175


import Candidate.Bundles.B176Part1
import Candidate.Bundles.B176Part2

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseFamily; sha256 9ab5aeb70109181eb2521fb5fab7c857dfc19e094fb893fa86c97e4dcf1ab307 -/
section
                                                                
                                                                 
                                                         
                                                      
                                                        

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentSecondEnergySplit CenteredMomentWholeDivisorShell
open CenteredMomentSourceRow CenteredMomentCommonPairedSource CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstSourceReduction
local notation "O" => HeckeFamily.O
attribute [local instance] geometryMainCoarseFamilySumDecidable

theorem actual_geometry_main_all_projector_coarse_family {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ plainCap)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤ loss)(hU : 0≤ U) :
    ∃K : ℝ,0< K ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |Dfirst|≤ B →
      |a|≤ B → |frequencyLoss Z 32 ξ+reserve|≤ B → (∀j,s.M j≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^plainCap) →
      (∀j,s.P j≤ Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(height : rows→ℝ)(Ds : rows→ Finset (Ideal O))
        (control B₁ B₂ : ℝ),0≤ control → 0≤ B₁ → 0≤ B₂ →
      (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let outer := fun r : rows=>(Kmain (first r.val.val.1.1)/volume (source r.val.val.1.1))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤ K*control*
        Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε) := by
  let exponent := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad
  let L := ((N:ℝ)+2)*U
  obtain ⟨K,hK,hfamily⟩ := actual_geometry_main_all_height_coarse_family
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε
  obtain ⟨Cp,hCp,hpayment⟩ := shared_projector_shell_payment L pad (by positivity) hpad
  refine ⟨Cp*K*(2:ℝ)^(3*ε),by positivity,?_⟩
  filter_upwards [hfamily,hpayment] with Z hfam hp
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector
    Kmain Tsec hprojector hz₁ hz₂ hKm Index datum block rows second W
    height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs outer cost
  let projectors := sharedProjectors Ds
  let columnCost := fun (r : rows) (D : Ideal O)=>
    geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
      (column r.val.val.1.1).val*outer r*highNormalizedRowCost second datum r.val (height r) {D}
  have houter : ∀r : rows,0≤ outer r := by
    intro r
    exact div_nonneg (mul_nonneg (div_nonneg (hKm _).le (volume_pos _).le)
      (normalizer_pos _ _ (datum r.val.val.1).hC _).le) (lowerFactor_pos N lo ap hlo hap).le
  have hnonneg : ∀r D,0≤ columnCost r D := by
    intro r D
    exact mul_nonneg (mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hKfirst bin _)
      (houter r)) (high_normalized_row_cost_nonneg second datum r.val (height r) {D})
  have hnorm : ∀r : rows,∀D∈Ds r,(D.absNorm:ℝ)≤ Z^L := by
    intro r D hD
    apply (second_datum_projector_cap (datum r.val.val.1) N Z U
      ((live_card_le (alloc r.val.val.1.1).val).trans hα) hZ.le hU
      (actual_child_pool_cap s (C r.val.val.1.1) R (alloc r.val.val.1.1)
        (χ r.val.val.1.1) t (Z^U) hpool) D (hDs r D hD).1).2
  have hscale n (hn : n∈selectedShells projectors) :=
    shared_projector_shell_scale Ds Z L hnorm n hn
  have hZpos : 0< Z := zero_lt_one.trans hZ
  let E := K*control*(2:ℝ)^(3*ε)*Z^(exponent+3*L*ε)
  have hE : 0≤ E := by dsimp [E]; positivity
  have hpay (n : ℤ)(hn : n∈selectedShells projectors) :
      (∑r : rows,∑D∈shell projectors n,columnCost r D)≤ E := by
    have h := hfam hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
      hM hwin hscales hP hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj alloc halloc
      rows second W height (fun _=>shell projectors n) control (dyadicScale n) B₁ B₂ hcontrol
      (hscale n hn).1 hB₁ hB₂ hW₁ hW₂ hcontrolB
      (fun _ D hD=>by
        have hd:=shared_projector_shell_gates Ds n D hD
        exact ⟨hd.1,hd.2.2⟩)
    have hleft : (∑r : rows,∑D∈shell projectors n,columnCost r D)=
        ∑r : rows,geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
          (column r.val.val.1.1).val*outer r*
          highNormalizedRowCost second datum r.val (height r) (shell projectors n) := by
      simp only [columnCost,highNormalizedRowCost,Finset.sum_singleton,Finset.mul_sum]
    rw [hleft]
    apply h.trans
    have hdyadic : 0< dyadicScale n := zero_lt_one.trans_le (hscale n hn).1
    have hpow : (2*dyadicScale n)^(3*ε)≤(2:ℝ)^(3*ε)*Z^(3*L*ε) := by
      calc
        _≤(2*Z^L)^(3*ε) := Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left (hscale n hn).2 (by norm_num)) (by positivity)
        _=_ := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZpos.le _),←Real.rpow_mul hZpos.le]
          congr 1
          ring
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK.le hcontrol))
      (Real.rpow_nonneg hZpos.le exponent)
    convert hp using 1
    dsimp [E]
    rw [Real.rpow_add hZpos]
    ring
  have h := hp.2 Ds (fun r D hD=>(hDs r D hD).2) hnorm columnCost E hnonneg hE hpay
  have hleft : (∑r : rows,cost r)=∑r : rows,∑D∈Ds r,columnCost r D := by
    simp only [cost,columnCost,highNormalizedRowCost,Finset.sum_singleton,Finset.mul_sum]
  rw [hleft]
  convert h using 1
  dsimp [E,exponent,L]
  rw [show B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε=
      pad+(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad+3*(((N:ℝ)+2)*U)*ε) by ring,
    Real.rpow_add hZpos]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_all_projector_coarse_family
end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseFamily -/
