import Candidate.Cycle62.Physical.InitialMass.SecondLabelDisintegration
import Candidate.Cycle62.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle62.Physical.InitialMass.SecondHighPayment

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle62Moment
open CompletedGauss CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

theorem actual_geometry_main_radius_interval {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(M Z ξ a reserve B : ℝ)
    (hZ : 1<Z)(hK : 0<Z^M)(hB : 0≤B)
    (hM : |M|≤B)(hA : |Real.logb Z (volume s)|≤B)(ha : |a|≤B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    Z^(-(16*B))≤firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j) ∧
    firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)≤Z^(16*B) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
  let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
  let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
  let A := Real.logb Z (volume s)
  have hv (i : Fin 5) : 0≤v i ∧ v i≤B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact ⟨Real.logb_nonneg hZ hh.1,
      (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2⟩
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (CenteredMomentAmplificationChildInput.volume_pos s)).symm
  have he : Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=v 4 := by
    change Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=
      Real.logb Z (Ideal.span {primeSubsetGenerator (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm
    rw [first_projector_span]
  have hR : Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm=v 3 := rfl
  have hC : Real.logb Z (l.1.1.absNorm:ℝ)=v 0 := rfl
  have hD : Real.logb Z (l.1.2.absNorm:ℝ)=v 1 := rfl
  rw [hV,actual_main_radius_power reflected l src.hC src.hD src.sameSupport Z M A a ξ reserve hZ]
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hR,he,hC,hD]
  all_goals
    have hm0 (i j : Fin 5) : 0≤max (v i-v j) 0 := le_max_right _ _
    have hmB (i j : Fin 5) : max (v i-v j) 0≤B :=
      max_le (by linarith [(hv i).2,(hv j).1]) hB
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).1,(abs_le.mp hM).2,(abs_le.mp ha).1,
        (abs_le.mp hω).1,(hv 0).2,(hv 1).2,(hv 3).1,(hv 4).1,hm0 0 1,hm0 1 0]
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).2,(abs_le.mp hM).1,(abs_le.mp ha).2,
        (abs_le.mp hω).2,(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2,hmB 0 1,hmB 1 0]

def geometryMainAbsoluteBox (Z : ℝ)(N : ℕ)(B loss b : ℝ) : Finset (Fin 4→ℤ) :=
  secondAbsoluteBox Z (16*B) (16*B) (B+loss) (B+loss) (b^(2*N))

private theorem actual_second_absolute_box_mem {α : Type*}[Fintype α][DecidableEq α]
    (Z A D₀ B L Cr : ℝ)(hZ : 1≤Z)(hA : 0≤A)(hD₀ : 0≤D₀)
    (hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr)
    (slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec ξ : ℝ)(hK : 0<K)
    (hKlo : Z^(-D₀)≤K)(hKhi : K≤Z^A)
    (hcut : frequencyRadius Tsec Z ξ≤Cr*Z^L)(hsource : sourceRadius s≤Z^B)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    actualSecondDyad s R seed K Tsec Z ξ q∈secondAbsoluteBox Z A D₀ B L Cr := by
  let d := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
  have hg := actual_retained_block_gates slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
  apply Fintype.mem_piFinset.mpr
  intro i
  exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
    d.C d.D d.hC d.hD d.sameSupport d.inactive K (frequencyRadius Tsec Z ξ) (sourceRadius s)
    hK hKlo hKhi hcut hsource
    (hg.2.2.1.trans hsource) (hg.2.2.2.trans hsource) q.2.2 i

theorem eventual_actual_geometry_main_absolute_box (N : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hb : 1≤b)(hbs : 1≤bs)
    (hξ : 0≤ξ)(hξloss : ξ≤loss)(hε : 0<ε) :
    ∃Cb : ℝ,0<Cb ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ((geometryMainAbsoluteBox Z N B loss b).card:ℝ)≤Cb*Z^ε ∧
      ∀{α : Type}[Fintype α][DecidableEq α](reflected : Bool)(s : Input α)(R seed : Ideal O)
        (M a reserve t : ℝ)(hK : 0<Z^M),
      Fintype.card α≤N → Endpoints b bs bs s → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      |Real.logb Z (volume s)|≤B → |M|≤B → |a|≤B →
      |frequencyLoss Z 32 ξ+reserve|≤B → 0≤a → 0≤reserve →
      ∀(key : ℤ×(Fin 5→ℤ))
        (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)),
      j∈firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus) →
      ∀alloc : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j),
      frozenCoefficient alloc.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j)
        R s.ν s.W s.P≠0 →
      let childSource := child s (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) R alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j) t
      let Kmain := firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      let Tsec := firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      ∀q : ActualSecondBlockIndex childSource
        (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) j.2.1.val Kmain Tsec Z ξ,
      actualSecondDyad childSource (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j)
        j.2.1.val Kmain Tsec Z ξ q∈geometryMainAbsoluteBox Z N B loss b := by
  have hCr : 0<b^(2*N) := pow_pos (zero_lt_one.trans_le hb) _
  obtain ⟨Cb,hCb,hcard⟩ := second_absolute_envelope_subpower
    (16*B) (16*B) (B+loss) (B+loss) (b^(2*N)) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hCr hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hcard,eventual_geometry_child_source_cap N b bs loss hb hbs hloss]
    with Z hc hs
  refine ⟨hs.1,?_,?_⟩
  · simpa only [geometryMainAbsoluteBox,second_absolute_box_card] using hc
  intro α _ _ reflected s R seed M a reserve t hK hn hend hseed hz₁ hz₂ hsource hA hM ha hω
    ha0 hreserve key j hj alloc halloc childSource Kmain Tsec q
  have hZ : 0<Z := zero_lt_one.trans hs.1
  have hV : volume s≤Z^B := (Real.logb_le_iff_le_rpow hs.1 (volume_pos s)).mp (abs_le.mp hA).2
  have hchild := hs.2 s B hn hend hV
    (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) R alloc
    (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j) t halloc
  have hradius := actual_geometry_main_radius_interval reflected s R seed M Z ξ a reserve B
    hs.1 hK hB hM hA ha hω hseed hz₁ hz₂ hsource key j
  have hcut := actual_geometry_main_cutoff_cap reflected s R seed (Z^M) Z ξ (3*a) reserve b M
    N hK hs.1 (zero_lt_one.trans_le hb) hξ (by positivity) hreserve le_rfl key j
  have hcut' : frequencyRadius Tsec Z ξ≤b^(2*N)*Z^(B+loss) := by
    apply hcut.trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hb) _)
    exact Real.rpow_le_rpow_of_exponent_le hs.1.le (by linarith [(abs_le.mp hM).2])
  exact actual_second_absolute_box_mem Z (16*B) (16*B) (B+loss) (B+loss) (b^(2*N)) hs.1.le
    (by positivity) (by positivity) (by positivity) (by positivity) hCr
    (liveIndices alloc.val) childSource (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) j.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK key)
      (fun _=>logAnnulus) j hj) hz₁ hz₂ Kmain Tsec ξ
    (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ _)
    hradius.1 hradius.2 hcut' hchild q

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_main_radius_interval
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_geometry_main_absolute_box
