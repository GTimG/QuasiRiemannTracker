/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B117
import Submissions.gao_cycle61_plane_20261013.Bundles.B120
import Submissions.gao_cycle61_plane_20261013.Bundles.B122
import Submissions.gao_cycle61_plane_20261013.Bundles.B132

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseFrequency; sha256 6ad9bcb8dacbecedea6cc8518407caf8ba4a452b6ca9aaf6fc8eaaef6cfe4174 -/
section
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplifiedRetainedRadius
open Cycle61Moment Cycle61HighFrequency CenteredMomentFirstScale
local notation "O" => HeckeFamily.O

theorem eventual_actual_joint_frequency_coarse (u₀ : O)(b ε : ℝ)(N : ℕ)
    (hb : 0< b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀(reflected left : Bool)(unit : FirstSourceLabel→ Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (hC : Supported l.val.1.1.1)(hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(K V a δ reserve ξ M Amax : ℝ),0< K → 0< V → ξ≤ε →
      K≤ Z^M → (l.val.1.1.1.absNorm:ℝ)≤ Z^Amax →
      0≤ a → 0≤δ → 0≤ reserve →
      let C := l.val.1.1.1
      let D := l.val.1.1.2
      let E := l.val.1.2.val
      let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
      let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
      let Kmain := mainCommonRadius Z d
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun p:CommonIndex C D=>p.val) E}) K V Z)
        c (3*a) δ reserve
      let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ
      let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
        nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
      retainedWeight R (normValue A)≠0 →
      normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤ Z^(M+5*Amax+ε) := by
  filter_upwards [eventual_actual_joint_frequency_budget u₀ b ε N hb hε] with Z h
  refine ⟨h.1,?_⟩
  intro reflected left unit l hC hD heq K V a δ reserve ξ M Amax hK hV hξ hKM hCA ha hδ hreserve
    C D E c d Kmain R A hret
  have hf := h.2 reflected left unit l hC hD heq K V a δ reserve ξ hK hV hξ hret
  have hlogK := Real.logb_le_logb_of_le h.1 hK hKM
  rw [Real.logb_rpow (zero_lt_one.trans h.1) h.1.ne'] at hlogK
  have hlogC := Real.logb_le_logb_of_le h.1 (norm_pos _ hC.1) hCA
  rw [Real.logb_rpow (zero_lt_one.trans h.1) h.1.ne'] at hlogC
  have hnum := first_numerator_log_le left l.val.1 hC hD Z h.1
  have hactive : 0≤ Real.logb Z (normValue (activeConductor C D)) := by
    apply Real.logb_nonneg h.1
    have hp := active_norm_pos C D
    change (1:ℝ)≤((Ideal.span {activeConductor C D}).absNorm:ℝ)
    have hn : 0<(Ideal.span {activeConductor C D}).absNorm := by exact_mod_cast hp
    exact_mod_cast hn
  apply hf.2.trans
  apply Real.rpow_le_rpow_of_exponent_le h.1.le
  dsimp only [C,D,c,d] at hactive ⊢
  linarith [le_max_right (Real.logb Z ((if reflected then l.val.1.1.2 else l.val.1.1.1).absNorm:ℝ)-
    Real.logb Z ((if reflected then l.val.1.1.1 else l.val.1.1.2).absNorm:ℝ)) 0]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_joint_frequency_coarse

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseFrequency -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryCoarseSupport; sha256 284a818d67628c95e35ecc1befd093a1104c10b9d1e1901fbc358672efaf3efe -/
section
                                                             
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

/-- The actual geometric parent and retained second row supply both the
coarse frequency cap and the full row-times-missing-radical support cap.
The threshold is chosen before every moving source and row. -/
theorem eventual_geometry_joint_support (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)(b ε : ℝ)(N : ℕ)(hb : 0< b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,∀hZ : 1< Z,
      ∀{ι α Label : Type}[Fintype ι][DecidableEq ι][Fintype α][DecidableEq α][Fintype Label]
        (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K ξ a reserve M A : ℝ)(hK : 0< K),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^A → K≤ Z^M →
      0≤ξ → ξ≤ε → 0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
        (r : secondLiveRows (fun l=>(d l).block))
        (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j),
      (d r.val.1).radius=frequencyRadius
        (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
          (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ →
      let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
      let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
      let l := secondEncodedNonzeroRow (fun k=>(d k).block) first r (!reflected) u₀ unit hf
      normValue (jointSourceRow (!reflected) u₀ unit l.val)≤ Z^(M+5*A+ε) ∧
        ((firstSourceMissing (!reflected) l.val.1).absNorm:ℝ)≤ Z^A ∧
        ((Ideal.span {jointSourceRow (!reflected) u₀ unit l.val}*
          firstSourceMissing (!reflected) l.val.1).absNorm:ℝ)≤ Z^(M+6*A+ε) := by
  filter_upwards [eventual_actual_joint_frequency_coarse u₀ b ε N hb hε] with Z h
  intro hZ ι α Label _ _ _ _ _ reflected s R seed K ξ a reserve M A hK hs hz₁ hz₂ hS hKM
    hξ hξε ha hreserve bin j d first r hfirst hradius unit hf l
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  have he : l.val.1=geometryFirstLabel s R seed K Z ξ hK bin j := hfirst
  have hc : Supported l.val.1.1.1 := by rw [he]; exact src.hC
  have hd : Supported l.val.1.1.2 := by rw [he]; exact src.hD
  have hsupp : CompletedGauss.primeSupport l.val.1.1.1=CompletedGauss.primeSupport l.val.1.1.2 := by
    rw [he]; exact src.sameSupport
  have hCcap : (l.val.1.1.1.absNorm:ℝ)≤ Z^A := by
    rw [he]
    exact (actual_geometry_norm_caps s R seed K Z ξ A hs hz₁ hz₂ hS j.1.val 0).2
  have hh := h.2 reflected (!reflected) (firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀)
    l hc hd hsupp K (volume s) a (frequencyLoss Z 32 ξ) reserve ξ M A hK (volume_pos s)
    hξε hKM hCcap ha (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hreserve
  have hret := actual_second_live_retained_weight (fun k=>(d k).block) r.val r.property
  have hn : normValue (jointSourceRow (!reflected) u₀ unit l.val)≤ Z^(M+5*A+ε) := by
    apply hh
    change retainedWeight
      (frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N l.val.1) Z ξ)
      (normValue ((d r.val.1).block.frequency*r.val.2.2.2.val))≠0
    rw [he,←hradius]
    exact hret

  have hm := joint_missing_support_cap (!reflected) u₀ unit l hc hd Z (M+5*A+ε) A
    (zero_lt_one.trans hZ) hn hCcap
  refine ⟨hn,hm.1,?_⟩
  convert hm.2 using 1 <;> congr 1 <;> ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_joint_support

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryCoarseSupport -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySelectedRows; sha256 3a88883911a467e31e2496a12e6fde6e2c533ecfee24c194d444db4ed2116985 -/
section
                                                      
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- The selected actual first common children feed the second joint-row
bound. All source-radius, cutoff, seed and dyad gates are derived from the
original source; distinct joint rows remain for the density estimate. -/
theorem actual_geometry_selected_row_budget (N : ℕ)(b bs ε Brow Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)(hBrow : 0≤ Brow)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K sigma reserve t : ℝ)(hK : 0< K),
      Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → K≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ sigma → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed K Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected K (volume s) Z ξ sigma reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ sigma reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let block := fun q : Index=>(actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2).block
      let label := fun q : Index=>first q.1
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)(hu₀ : u₀≠0)(hunit : ∀l,unit l≠0),
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(cost : rows→ℝ)(E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow block label r.val)}).absNorm:ℝ)≤ Z^Brow) → (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤(D*Z^(2*ε))*E := by
  obtain ⟨D,hD,hrows⟩ := actual_retained_source_row_budget Brow (Amax+ε) (Mmax+ξ/2) (b^(2*N)) ε
    hBrow (by positivity) (by positivity) (by positivity) hε
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows,eventual_geometry_child_source_cap N b bs ε hb hbs hε] with Z hz hchild
  intro hZ α Label _ _ _ reflected s R seed K sigma reserve t hK hcard he hV hKM
    hs₁ hs₂ hsigma hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index block label left u₀ unit hu₀ hunit hf rows cost E hnorm hcost key hpick
  exact hz.2 slots source (fun l=>R*C l) projector hprojector hz₁ hz₂ first Kmain Tsec ξ
    (Z^(Amax+ε)) hKm hinj
    (fun l=>hchild.2 s Amax hcard he hV (C l) R (alloc l) (χ l) t (halloc l)) le_rfl
    (fun l=>actual_geometry_main_cutoff_cap reflected s R seed K Z ξ sigma reserve b Mmax N
      hK hZ (zero_lt_one.trans_le hb) hξ hsigma hreserve hKM bin (column l).val)
    left u₀ unit hf rows cost E hnorm hcost hpick

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_row_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySelectedRows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryClosedRowBudget; sha256 d3f802667f7169de44bf768e55eacc6da7ddac2d5ff378f99c2eee5863902ee8 -/
section
                                                        
                                                      
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

/-- Joint row selection for actual geometry, with the coarse frequency bound
derived from the source and retained support. Only the selected joint energy
remains as an analytic input. -/
theorem actual_geometry_closed_row_budget (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0< K),
      Squarefree seed → Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → K≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed K Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected K (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let block := fun q : Index=>(actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun l=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(cost : rows→ℝ)(E : ℝ),
      (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤(D*Z^(2*ε))*E := by
  obtain ⟨D,hD,hrows⟩ := actual_geometry_selected_row_budget N b bs ε
    (Mmax+5*Amax+6*ε) Amax Mmax ξ hb hbs hε (by positivity) hA hM hξ
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows,eventual_geometry_joint_support η₀ u₀ F₀ R₀ hu₀ b ε N
    (zero_lt_one.trans_le hb) hε,
    (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (b^N*bs*bs))] with Z hz hsupport hconstant
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index block label left unit hunit hf rows cost E hcost key hpick
  have hS : sourceRadius s≤ Z^(Amax+ε) := by
    calc
      _≤(b^N*bs*bs)*volume s := (radius_bound N b bs bs hb hbs hbs s hcard he).2
      _≤ Z^ε*Z^Amax := mul_le_mul hconstant hV (volume_pos s).le (by positivity)
      _=_ := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]
  apply hz hZ reflected s R seed K (3*a) reserve t hK hcard he hV hKM
    hs₁ hs₂ (by positivity) hreserve bin column hinj alloc halloc left u₀ unit hu₀ hunit
    rows cost E _ hcost hpick
  intro r
  let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
    (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
  have hh := hsupport hZ reflected s R seed K ξ a reserve Mmax (Amax+ε) hK hseed hs₁ hs₂
    hS hKM hξ hξε ha hreserve bin (column r.val.val.1.1).val datum label r.val rfl rfl
  dsimp only at hh
  change CenteredMomentSectorLocalization.normValue (jointSourceRow left u₀ unit
    (secondEncodedRow block label r.val))≤ _
  convert hh.1 using 1 <;> congr 1 <;> ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_closed_row_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryClosedRowBudget -/
