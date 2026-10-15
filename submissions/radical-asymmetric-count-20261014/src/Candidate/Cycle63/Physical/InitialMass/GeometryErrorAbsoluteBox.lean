import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorScalarPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAdmission

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
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
open CenteredMomentFirstCanonicalFamily Cycle63Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O

theorem actual_geometry_error_radius_interval {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(M Z ξ a reserve B : ℝ)
    (hZ : 1<Z)(hK : 0<Z^M)(hB : 0≤B)
    (hM : |M|≤B)(hA : |Real.logb Z (volume s)|≤B)(ha : |a|≤B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key))
    (p : O)(hp : p≠0)(k : ℕ)(hk : 1≤k) :
    Z^(-(16*B))≤firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      Z M (volume s) a (frequencyLoss Z 32 ξ) reserve p k ∧
    firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      Z M (volume s) a (frequencyLoss Z 32 ξ) reserve p k≤Z^(16*B) := by
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
  have hp0 : 0≤Real.logb Z (normValue p) :=
    Real.logb_nonneg hZ (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hmove : errorMoving p Z k≤2*errorRemoval p Z k := by
    have hkR : (1:ℝ)≤k := by exact_mod_cast hk
    unfold errorMoving errorRemoval
    split_ifs <;> nlinarith
  have hrem0 : 0≤errorRemoval p Z k := by unfold errorRemoval; positivity
  rw [hV,actual_error_radius_power reflected l src.hC src.hD src.sameSupport
    Z M A a (frequencyLoss Z 32 ξ) reserve p k hZ]
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hR,he,hC,hD]
  all_goals
    have hm0 (i j : Fin 5) : 0≤max (v i-v j-2*errorRemoval p Z k+errorMoving p Z k) 0 := le_max_right _ _
    have hmB (i j : Fin 5) : max (v i-v j-2*errorRemoval p Z k+errorMoving p Z k) 0≤B :=
      max_le (by linarith [(hv i).2,(hv j).1]) hB
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).1,(abs_le.mp hM).2,(abs_le.mp ha).1,
        (abs_le.mp hω).1,(hv 0).2,(hv 1).2,(hv 3).1,(hv 4).1,hm0 0 1,hm0 1 0]
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).2,(abs_le.mp hM).1,(abs_le.mp ha).2,
        (abs_le.mp hω).2,(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2,hmB 0 1,hmB 1 0]

def geometryErrorAbsoluteBox (Z : ℝ)(N : ℕ)(B loss b : ℝ) : Finset (Fin 4→ℤ) :=
  secondAbsoluteBox Z (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N))

/-- The Fourier expression retains the actual source slot count. Only its
fixed polynomial envelope uses the ambient cap. -/
theorem actual_geometry_error_cutoff_cap {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(B loss b : ℝ)(_hB : 0≤B)(hloss : 0≤loss)(hb : 1≤b)
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(Z M amp ξ reserve _t : ℝ)(hZ : 1<Z)
    (hn : Fintype.card α≤N)(hξ : ξ≤loss)(hV : volume s≤Z^B)
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O)(hp : p≠0)(i : Fin 3)
    (hrad : Z^(-(16*B))≤geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i) :
    frequencyRadius (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b
      (Fintype.card α) hZ bin q p i) Z ξ≤b^(2*N)*Z^(18*B+loss) := by
  let I:=geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  have hI : (1:ℝ)≤I.absNorm := norm_ge_one _ (allocation_ne s I q.2)
  have hpN : (1:ℝ)≤(normValue p)^(errorIndex i+1) :=
    one_le_pow₀ (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hb0 : 0<b:=zero_lt_one.trans_le hb
  have hv0 := volume_pos s
  have hi0 := zero_lt_one.trans_le hI
  have hp0 := zero_lt_one.trans_le hpN
  have hnum : b^(Fintype.card α)*volume s/((I.absNorm:ℝ)*(normValue p)^(errorIndex i+1))
      ≤b^N*Z^B := by
    calc
      _≤b^(Fintype.card α)*volume s := div_le_self (by positivity)
        (one_le_mul_of_one_le_of_one_le hI hpN)
      _≤b^N*Z^B := mul_le_mul (pow_le_pow_right₀ hb hn) hV (volume_pos s).le (by positivity)
  have hnum0 : 0≤b^(Fintype.card α)*volume s/((I.absNorm:ℝ)*(normValue p)^(errorIndex i+1)) := by positivity
  unfold frequencyRadius geometryErrorFourierScale
  change (_ / geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)*Z^(ξ/2)≤_
  calc
    _≤((b^N*Z^B)^2/Z^(-(16*B)))*Z^(ξ/2) := mul_le_mul_of_nonneg_right
      (div_le_div₀ (by positivity) (pow_le_pow_left₀ hnum0 hnum 2)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hrad) (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _=b^(2*N)*Z^(18*B+ξ/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
        mul_div_assoc,←Real.rpow_sub (zero_lt_one.trans hZ),mul_assoc,
        ←Real.rpow_add (zero_lt_one.trans hZ)]
      rw [←pow_mul,show N*2=2*N by omega]
      congr 1
      ring_nf
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)

/-- Supported extraction retains the exact prime power denominator; it can
only decrease the coarse source envelope. -/
theorem eventual_geometry_error_child_source_cap (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (s : Input α)(A : ℝ),Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^A →
      ∀(C R : Ideal O)(B₁ : actualAllocations s.pools C)(τ : Character)(t : ℝ),
      frozenCoefficient B₁.val C R s.ν s.W s.P≠0 →
      ∀(p : O),p≠0 → ∀k : ℕ,
      (∀i I,I∈(child s C R B₁ τ t).slots i→IsCoprime (Ideal.span {p}) I) →
      ∀(Bp : actualAllocations (child s C R B₁ τ t).pools ((Ideal.span {p})^k))
        (υ : Character)(v : ℝ),
      sourceRadius (twiceChild s C R B₁ τ t (Ideal.span {p}) k Bp υ v)≤Z^(A+loss) := by
  filter_upwards [(tendsto_rpow_atTop hloss).eventually
    (eventually_ge_atTop (geometry N b bs bs)),eventually_gt_atTop (1:ℝ)] with Z hg hZ
  refine ⟨hZ,?_⟩
  intro α _ _ s A hn hend hV C R B₁ τ t hf p hp k hcop Bp υ v
  have hc:=twice_caps N b bs bs hb hbs hbs s hn hend C R B₁ τ t hf
    (Ideal.span {p}) (Ideal.span_singleton_eq_bot.not.mpr hp) k hcop Bp υ v
  have hden := one_le_mul_of_one_le_of_one_le (norm_ge_one C (allocation_ne s C B₁))
    (one_le_pow₀ (n:=k) (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hrad : sourceRadius (twiceChild s C R B₁ τ t (Ideal.span {p}) k Bp υ v)≤
      geometry N b bs bs*volume s/((C.absNorm:ℝ)*((Ideal.span {p}).absNorm:ℝ)^k) := by
    simpa only [mul_div_assoc] using hc.2.2.2
  calc
    _≤geometry N b bs bs*volume s := hrad.trans (div_le_self
      (mul_nonneg ((geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)) (volume_pos s).le) hden)
    _≤Z^loss*Z^A := mul_le_mul hg hV (volume_pos s).le (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _=Z^(A+loss) := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

/-- One fixed box covers all literal extracted sources, allocations,
heights and second blocks. The Fourier scale uses card α, not its cap N. -/
theorem eventual_actual_geometry_error_absolute_box (N : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hb : 1≤b)(hbs : 1≤bs)
    (hξ : ξ≤loss)(hε : 0<ε) :
    ∃Cb : ℝ,0<Cb ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ((geometryErrorAbsoluteBox Z N B loss b).card:ℝ)≤Cb*Z^ε ∧
      ∀{α : Type}[Fintype α][DecidableEq α](reflected : Bool)(s : Input α)(R seed : Ideal O)
        (M amp reserve t : ℝ)(hZ : 1<Z),
      Fintype.card α≤N → Endpoints b bs bs s → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      |Real.logb Z (volume s)|≤B → |M|≤B → |amp|≤B →
      |frequencyLoss Z 32 ξ+reserve|≤B →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀(p : O),p≠0 → ∀(i : Fin 3),
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I) →
      ∀(Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ),
      let extracted:=geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v
      let rad:=geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i
      let fourier:=geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i
      let Rsecond:=(R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
      Z^(-(16*B))≤rad ∧ rad≤Z^(16*B) ∧ sourceRadius extracted≤Z^(B+loss) ∧
        frequencyRadius fourier Z ξ≤b^(2*N)*Z^(18*B+loss) ∧
        ∀z : ActualSecondBlockIndex extracted Rsecond q.1.val.2.1.val rad fourier Z ξ,
          actualSecondDyad extracted Rsecond q.1.val.2.1.val rad fourier Z ξ z∈
            geometryErrorAbsoluteBox Z N B loss b := by
  have hCr : 0<b^(2*N):=pow_pos (zero_lt_one.trans_le hb) _
  obtain ⟨Cb,hCb,hcard⟩:=second_absolute_envelope_subpower
    (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N)) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hCr hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hcard,eventual_geometry_error_child_source_cap N b bs loss hb hbs hloss]
    with Z hc hs
  refine ⟨hs.1,?_,?_⟩
  · simpa only [geometryErrorAbsoluteBox,second_absolute_box_card] using hc
  intro α _ _ reflected s R seed M amp reserve t hZ hn hend hseed hz₁ hz₂
    hsource hA hM ha hω bin q hf p hp i hcop Bp υ v extracted rad fourier Rsecond
  have hz0 := zero_lt_one.trans hZ
  have hK := Real.rpow_pos_of_pos hz0 M
  have hV : volume s≤Z^B :=
    (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hr := actual_geometry_error_radius_interval reflected s R seed M Z ξ amp reserve B
    hZ hK hB hM hA ha hω hseed hz₁ hz₂ hsource bin q.1.val p hp (errorIndex i+1)
    (Nat.succ_le_succ (Nat.zero_le _))
  have hr' : Z^(-(16*B))≤rad ∧ rad≤Z^(16*B) := by
    simpa only [rad,geometryErrorSourceRadius,actual_geometry_error_tail_radius] using hr
  have hcut := actual_geometry_error_cutoff_cap N B loss b hB hloss.le hb
    reflected s R seed Z M amp ξ reserve t hZ hn hξ hV bin q p hp i hr'.1
  have hextracted : sourceRadius extracted≤Z^(B+loss) :=
    hs.2 s B hn hend hV _ R q.2 _ t hf p hp (errorIndex i+1) hcop
      (errorActiveAllocation _ _ Bp) υ v
  refine ⟨hr'.1,hr'.2,hextracted,hcut,?_⟩
  intro z
  have hseed1 := actual_first_live_squarefree
    (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus) q.1.val q.1.property
  have hradpos := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ bin q p i
  let d:=actualSecondBlockDatum _ extracted Rsecond q.1.val.2.1.val hseed1 hz₁ hz₂ rad fourier Z ξ hradpos z
  have hg:=actual_retained_block_gates _ extracted Rsecond q.1.val.2.1.val hseed1 hz₁ hz₂ rad fourier Z ξ hradpos z
  apply Fintype.mem_piFinset.mpr
  intro c
  exact actual_second_dyads_absolute Z (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N)) hZ.le
    (by positivity) (by positivity) (by positivity) (by positivity) hCr
    d.C d.D d.hC d.hD d.sameSupport d.inactive rad (frequencyRadius fourier Z ξ) (sourceRadius extracted)
    hradpos hr'.1 hr'.2 hcut hextracted (hg.2.2.1.trans hextracted) (hg.2.2.2.trans hextracted) z.2.2 c

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_error_radius_interval
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_error_cutoff_cap
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_geometry_error_child_source_cap

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_error_absolute_box
