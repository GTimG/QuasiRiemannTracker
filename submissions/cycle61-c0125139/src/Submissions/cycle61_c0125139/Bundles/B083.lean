/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B081
import Submissions.cycle61_c0125139.Bundles.B082

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryPayment; sha256 30aaf42ac191a6101e2f2f41521fcd01c86292364d1124f36f44d606dff3ea6a -/
section
                                                
                                                 

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O

/-- The coordinates are c,d,p,R,E, all taken from the actual first label. -/
def leftExponent (A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v 2+A-v 0+v 3+v 4+max (3*v 0-5*v 1-v 3) 0/6

def rightExponent (A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v 2+A-v 1+v 3+v 4+max (3*v 1-5*v 0-v 3) 0/6

def outsideExponent (M A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  M-A-v 3/2-v 4

lemma allowance_variation (v u : Fin 5 → ℝ) (w : ℝ) (hw : 0≤ w)
    (hd : ∀i, v i-u i≤ w ∧ u i-v i≤ w) (i j : Fin 5) :
    max (3*v i-5*v j-v 3) 0/6 ≤ max (3*u i-5*u j-u 3) 0/6+3*w/2 := by
  have hmax : max (3*v i-5*v j-v 3) 0 ≤ max (3*u i-5*u j-u 3) 0+9*w := by
    apply max_le
    · have hh := le_max_left (3*u i-5*u j-u 3) (0:ℝ)
      linarith [(hd i).1,(hd j).2,(hd 3).2]
    · have hh := le_max_right (3*u i-5*u j-u 3) (0:ℝ)
      linarith
  linarith

/-- The left scalar is kept inside its square sum. Cross-label products
within one geometry bin lose at most five bin widths in their exponent. -/
lemma cross_exponent_payment (v u r : Fin 5 → ℝ) (M A w : ℝ) (hw : 0≤ w)
    (hv : ∀i, v i-u i≤ w ∧ u i-v i≤ w)
    (hr : ∀i, r i-u i≤ w ∧ u i-r i≤ w)
    (hbase : outsideExponent M A u+(leftExponent A u+rightExponent A u)/2≤ M) :
    outsideExponent M A v+(leftExponent A v+rightExponent A r)/2≤ M+5*w := by
  have hl := allowance_variation v u w hw hv 0 1
  have hr' := allowance_variation r u w hw hr 1 0
  have hleft : 2*outsideExponent M A v+leftExponent A v ≤
      2*outsideExponent M A u+leftExponent A u+9*w/2 := by
    dsimp [outsideExponent,leftExponent]
    linarith [(hv 2).1,(hv 0).2,(hv 4).2]
  have hright : rightExponent A r≤ rightExponent A u+11*w/2 := by
    dsimp [rightExponent]
    linarith [(hr 2).1,(hr 1).2,(hr 3).1,(hr 4).1]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryPaymentSumDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma actual_geometry_fiber_difference (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1< Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (key : ℤ×(Fin 5→ℤ))
    (q r : CommonGeometryFiber s R seed K Z ξ key) (i : Fin 5) :
    geometryExponents s R seed K Z ξ q.val i-geometryExponents s R seed K Z ξ r.val i≤
      Real.logb Z 2 := by
  have hq := actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key q i
  have hr := actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key r i
  nlinarith

omit [DecidableEq ι] in
/-- The single-label balance is used only after the five arithmetic
coordinates have been frozen to one common bin. -/
lemma actual_geometry_balance (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ)
    (hZ : 1< Z) (q : FirstSourceCoordinate s R seed K Z ξ) :
    outsideExponent M A (geometryExponents s R seed K Z ξ q)+
      (leftExponent A (geometryExponents s R seed K Z ξ q)+
       rightExponent A (geometryExponents s R seed K Z ξ q))/2≤ M := by
  have hsup : CanonicalQuadraticSieve.Supported q.1.val.1 ∧
      CanonicalQuadraticSieve.Supported q.1.val.2 := CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) q.1.val.1 q.1.val.2 q.1.property
  have hc := actual_labels_commonPart s R seed K Z ξ q
  have hh := Cycle61.Physical.actual_joint_side_exponent q.1.val.1 q.1.val.2 hsup.1 hsup.2
    Z M A (geometryExponents s R seed K Z ξ q 4) hZ
  dsimp only at hh
  rw [hc.1,hc.2] at hh
  change outsideExponent M A (geometryExponents s R seed K Z ξ q)+
    (leftExponent A (geometryExponents s R seed K Z ξ q)+
      rightExponent A (geometryExponents s R seed K Z ξ q))/2≤ M at hh
  exact hh

omit [DecidableEq ι] in
/-- Uniform cross-label payment. The left and right labels may differ;
no sum of per-label Cauchy estimates is substituted for joint Cauchy. -/
theorem actual_geometry_cross_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1< Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q r : CommonGeometryFiber s R seed K Z ξ key) :
    Z^(outsideExponent M A (geometryExponents s R seed K Z ξ q.val))*
      Real.sqrt (Z^(leftExponent A (geometryExponents s R seed K Z ξ q.val)))*
      Real.sqrt (Z^(rightExponent A (geometryExponents s R seed K Z ξ r.val))) ≤
        32*Z^M := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hw : 0≤ Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := cross_exponent_payment
    (geometryExponents s R seed K Z ξ q.val)
    (geometryExponents s R seed K Z ξ q.val)
    (geometryExponents s R seed K Z ξ r.val) M A (Real.logb Z 2) hw
    (fun i => ⟨by simpa using hw,by simpa using hw⟩)
    (fun i => ⟨hdiff r q i,hdiff q r i⟩)
    (actual_geometry_balance s R seed K Z ξ M A hZ q.val)
  have hp : Z^(M+5*Real.logb Z 2)=32*Z^M := by
    rw [Real.rpow_add hz,show 5*Real.logb Z 2=Real.logb Z 2*5 by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [←hp]
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith


/-- Pairwise control of the geometric weights pays the product of the two
whole energy sums. There is no cardinality loss for either finite family. -/
lemma weighted_joint_energy {I J : Type*} [Fintype I] [Fintype J]
    (p L : I→ℝ) (q R : J→ℝ) (C : ℝ)
    (hp : ∀i,0≤ p i) (hq : ∀j,0≤ q j) (hL : ∀i,0≤ L i) (hR : ∀j,0≤ R j)
    (hC : 0≤ C) (hpair : ∀i j,p i*q j≤ C^2) :
    Real.sqrt (∑i,p i*L i)*Real.sqrt (∑j,q j*R j) ≤
      C*Real.sqrt (∑i,L i)*Real.sqrt (∑j,R j) := by
  have hb : (∑i,p i*L i)*(∑j,q j*R j)≤ C^2*(∑i,L i)*(∑j,R j) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_right (hpair j i) (mul_nonneg (hL j) (hR i))
    nlinarith only [hh]
  have hl₀ : 0≤∑i,L i := Finset.sum_nonneg (fun i _=>hL i)
  have hr₀ : 0≤∑j,R j := Finset.sum_nonneg (fun j _=>hR j)
  have hl₁ : 0≤∑i,p i*L i := Finset.sum_nonneg (fun i _=>mul_nonneg (hp i) (hL i))
  have hr₁ : 0≤∑j,q j*R j := Finset.sum_nonneg (fun j _=>mul_nonneg (hq j) (hR j))
  have hs₁ : (Real.sqrt (∑i,p i*L i)*Real.sqrt (∑j,q j*R j))^2=
      (∑i,p i*L i)*(∑j,q j*R j) := by
    rw [mul_pow,Real.sq_sqrt hl₁,Real.sq_sqrt hr₁]
  have hs₀ : (C*Real.sqrt (∑i,L i)*Real.sqrt (∑j,R j))^2=
      C^2*(∑i,L i)*(∑j,R j) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hl₀,Real.sq_sqrt hr₀]
  have hnonneg : 0≤ C*Real.sqrt (∑i,L i)*Real.sqrt (∑j,R j) := by positivity
  nlinarith only [hb,hs₁,hs₀,hnonneg]

omit [DecidableEq ι] in
/-- The actual first scalar stays on the left of joint Cauchy. Normalized
left and right energies are still summed over every label in the bin. -/
theorem actual_geometry_joint_energy {I J : Type*} [Fintype I] [Fintype J] (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1< Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ))
    (left : I→ CommonGeometryFiber s R seed K Z ξ key)
    (right : J→ CommonGeometryFiber s R seed K Z ξ key) (L : I→ℝ) (N : J→ℝ)
    (hL : ∀q,0≤ L q) (hN : ∀q,0≤ N q) :
    Real.sqrt (∑q,Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ (left q).val)+
        leftExponent A (geometryExponents s R seed K Z ξ (left q).val))*L q)*
      Real.sqrt (∑q,Z^(rightExponent A (geometryExponents s R seed K Z ξ (right q).val))*N q) ≤
        32*Z^M*Real.sqrt (∑q,L q)*Real.sqrt (∑q,N q) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  apply weighted_joint_energy _ _ _ _ _ (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) hL hN (by positivity)
  intro q r
  have hh := actual_geometry_cross_payment s R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key (left q) (right r)
  have hsquared := pow_le_pow_left₀ (by positivity) hh 2
  rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
    Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
    ←Real.rpow_add hz] at hsquared
  convert hsquared using 1
  congr 2
  ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_cross_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_joint_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryContraction; sha256 9086f4bc8c41adc4cb0cd159f687cb22942ec2d0b40954474860806db1634a29 -/
section
                                                  
                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstChildBound
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstReduced CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentFirstSourceReduction
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow FourierBridge Cycle61Moment RayFourExpansion CenteredMomentPrimitive CenteredMomentScale
local notation "O" => HeckeFamily.O

lemma weighted_joint_energy_finset {I J : Type*} (S : Finset I) (T : Finset J)
    (p L : I→ℝ) (q N : J→ℝ) (C : ℝ)
    (hp : ∀i,0≤ p i) (hq : ∀j,0≤ q j) (hL : ∀i,0≤ L i) (hN : ∀j,0≤ N j)
    (hC : 0≤ C) (hpair : ∀i j,p i*q j≤ C^2) :
    Real.sqrt (∑i∈S,p i*L i)*Real.sqrt (∑j∈T,q j*N j)≤
      C*Real.sqrt (∑i∈S,L i)*Real.sqrt (∑j∈T,N j) := by
  have hh := weighted_joint_energy (fun i : S=>p i.val) (fun i : S=>L i.val)
    (fun j : T=>q j.val) (fun j : T=>N j.val) C
    (fun i=>hp i.val) (fun j=>hq j.val) (fun i=>hL i.val) (fun j=>hN j.val)
    hC (fun i j=>hpair i.val j.val)
  rw [Finset.sum_coe_sort S (fun i=>p i*L i),
    Finset.sum_coe_sort T (fun j=>q j*N j),
    Finset.sum_coe_sort S L,Finset.sum_coe_sort T N] at hh
  exact hh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def geometryFirstSource (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (r : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s R seed K Z ξ r) :=
  originalFirstBlock s R seed K Z ξ hK q.val

def geometryFirstPhase (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (r : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s R seed K Z ξ r) :=
  normPhase (coordinateBlock s R seed W K Z ξ q.val)

/-- Actual physical mass is contracted over each actual common geometry and ratio group, with
all first labels inside the matched column energy. -/
theorem actual_physical_mass_geometry_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
      (E : ℤ×(Fin 5→ℤ) → ℝ), (∀r∈commonGeometryBins s R seed K Z ξ, 0≤ E r) →
      (∀r∈commonGeometryBins s R seed K Z ξ, ∀t : ℝ,
        firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK r)
          (geometryFirstPhase s R seed W K Z ξ r) (fun _ => logAnnulus) t ≤
          E r*(1+‖t‖)^J) →
      physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*∑r∈commonGeometryBins s R seed K Z ξ, E r/(1+dyadicScale r.1)^A := by
  obtain ⟨C,hC,hbound⟩ := actual_first_active_contraction W (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => Real.log_nonneg (by norm_num))
    (fun _ _ hn => CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro s R seed K Z ξ hK E hE he
  rw [actual_physical_mass_geometry_groups,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hh := hbound (geometryFirstSource s R seed K Z ξ hK r)
    (geometryFirstPhase s R seed W K Z ξ r) (dyadicScale r.1) (dyadicScale_pos r.1)
    (fun q => actual_source_ratio_fiber s R seed K Z ξ r.1
      ⟨q.val,commonGeometryFiber_ratio s R seed K Z ξ r q⟩)
    (fun q => logAnnulus_norm _) (fun q => logAnnulus_norm _) (E r) (hE r hr) (he r hr)
  have hp : 0<(1+dyadicScale r.1)^A := pow_pos (by linarith [dyadicScale_pos r.1]) _
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  have hv (q : CommonGeometryFiber s R seed K Z ξ r) :
      (geometryFirstSource s R seed K Z ξ hK r q).value W (fun _ => logAnnulus) =
        coordinateBlock s R seed W K Z ξ q.val := rfl
  simpa only [geometryFirstPhase,hv,mul_comm] using hh



/-- Literal normalized left energy: the original phase and outside scalar
are inside the square, and only the proven geometric power is divided out. -/
def geometryLeftEnergy (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.leftColumn Finset.univ
      (firstJointLeft (geometryFirstSource s R seed K Z ξ hK key) weight q)
      (V 2) (firstLeftLog (geometryFirstSource s R seed K Z ξ hK key q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
        leftExponent A (geometryExponents s R seed K Z ξ q.1.val))

def geometryRightEnergy (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ)) (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.rightColumn Finset.univ
      (firstJointRight (geometryFirstSource s R seed K Z ξ hK key) q)
      (V 3) (firstRightLog (geometryFirstSource s R seed K Z ξ hK key q.1)) t‖^2/
      Z^(rightExponent A (geometryExponents s R seed K Z ξ q.1.val))

omit [DecidableEq ι] in
/-- Applies the cross-label payment to the actual joint first-sector energy.
All divisor, ray and frequency indices remain in the two normalized sums. -/
theorem actual_first_energy_geometry_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hK : 0< K) (hZ : 1< Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) :
    firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK key) weight V t ≤
      32*Z^M*Real.sqrt (geometryLeftEnergy s R seed K Z ξ M A hK key weight V t)*
        Real.sqrt (geometryRightEnergy s R seed K Z ξ A hK key V t) := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let L : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft src weight q)
      (V 2) (firstLeftLog (src q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
        leftExponent A (geometryExponents s R seed K Z ξ q.1.val))
  let N : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight src q)
      (V 3) (firstRightLog (src q.1)) t‖^2/
      Z^(rightExponent A (geometryExponents s R seed K Z ξ q.1.val))
  have hz : 0< Z := zero_lt_one.trans hZ
  let p (q : FirstSector src) := Z^(2*outsideExponent M A
    (geometryExponents s R seed K Z ξ q.1.val)+
      leftExponent A (geometryExponents s R seed K Z ξ q.1.val))
  let r (q : FirstSector src) := Z^(rightExponent A (geometryExponents s R seed K Z ξ q.1.val))
  have hpair (q u : FirstSector src) : p q*r u≤(32*Z^M)^2 := by
    have hh := actual_geometry_cross_payment s R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key q.1 u.1
    have hp := pow_le_pow_left₀ (by positivity) hh 2
    rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
      Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz] at hp
    convert hp using 1
    dsimp [p,r]
    congr 2
    ring
  have hh := weighted_joint_energy_finset (firstActiveSectors src V) (firstActiveSectors src V)
    p L r N (32*Z^M) (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) (fun _=>by dsimp [L];positivity)
    (fun _=>by dsimp [N];positivity) (by positivity) hpair
  simpa only [p,r,L,N,mul_div_cancel₀ _ (Real.rpow_pos_of_pos hz _).ne',
    firstActiveEnergyPair,geometryLeftEnergy,geometryRightEnergy,src] using hh


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_geometry_contraction

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_energy_geometry_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.JointWindowEnergy; sha256 4e7be31dd472957558c794f2bbb60be75faaeecf86e92cb1938e374cd27ed21d -/
section
                                              
                                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy FourierBridge
local notation "O" => HeckeFamily.O

lemma finite_set_weighted_integral_energy {κ : Type*} (S : Finset κ)
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (w : ℝ→ℝ) (hw : ∀t,0< w t)
    (E : ℝ) (hE : 0≤ E) (hb : Integrable (fun t=>w t*‖b t‖))
    (hφ : ∀k,Integrable (fun t=>b t*φ k t))
    (hbound : ∀t,(∑k∈S,‖φ k t‖^2)≤ E*(w t)^2) :
    (∑k∈S,‖∫t : ℝ,b t*φ k t‖^2)≤ E*(∫t : ℝ,w t*‖b t‖)^2 := by
  have hh := finite_weighted_integral_energy b (fun k : S=>φ k.val) w hw E hE hb
    (fun k=>hφ k.val) (fun t=>by
      rw [Finset.sum_coe_sort S (fun k=>‖φ k t‖^2)]
      exact hbound t)
  rw [Finset.sum_coe_sort S (fun k=>‖∫t : ℝ,b t*φ k t‖^2)] at hh
  exact hh

/-- The full first-column Hilbert index is retained through Mellin
integration. The source estimate is joint before integration; no individual
label energy envelope or label-count factor is introduced. -/
theorem actual_joint_first_window_energy {Label ι : Type*} [Fintype Label] [Fintype ι]
    (labels : Finset Label) (s : Label→ Input ι) (R seed C L : Label→ Ideal O) (hC : ∀l,Supported (C l))
    (hseed : ∀l,seed l∣C l) (τ : Label→ Character) (t T θ X : Label→ℝ)
    (hX : ∀l,0< X l) (z : Label→ O) (scalar : Label→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (henergy : ∀u : ℝ,
      (∑l∈labels,‖scalar l*allocatedPolynomial
        (CenteredMomentAmplificationChildInput.original (s l) (R l) (seed l))
        (C l) (L l) (τ l) (t l+2*Real.pi*(u-θ l)) (T l) (z l)‖^2)≤
          E*(1+‖u‖)^(2*J)) :
    (∑l∈labels,‖scalar l*(Real.sqrt (T l):ℂ)⁻¹*commonWindow
      (CenteredMomentAmplificationChildInput.original (s l) (R l) (seed l))
      (C l) (hC l) (τ l) (t l) (θ l) (X l) V (L l) (z l)‖^2)≤
        E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  let src (l : Label) := CenteredMomentAmplificationChildInput.original (s l) (R l) (seed l)
  let φ (l : Label) (u : ℝ) := logPhase (θ l-u) (Real.log (X l))*
    (scalar l*allocatedPolynomial (src l) (C l) (L l) (τ l)
      (t l+2*Real.pi*(u-θ l)) (T l) (z l))
  have hi (l : Label) : Integrable (fun u=>columnDensity V hc hs u*φ l u) := by
    have hh := (common_window_original_integrable (src l) (s l).pools_ne (s l).prime
      (C l) (hC l) (hseed l) (τ l) (t l) (T l) (θ l) (X l) (hX l)
      V hc hs (L l) (z l)).const_mul (scalar l)
    convert hh using 1
    funext u
    dsimp [φ,allocatedPolynomial]
    ring
  have hb (u : ℝ) : (∑l∈labels,‖φ l u‖^2)≤ E*((1+‖u‖)^J)^2 := by
    simpa only [φ,norm_mul,logPhase_norm,one_mul,src,←pow_mul,Nat.mul_comm] using henergy u
  have hbound := finite_set_weighted_integral_energy labels (columnDensity V hc hs) φ
    (fun u=>(1+‖u‖)^J) (fun _=>by positivity) E hE
    (columnDensity_moments V hc hs J) hi hb
  have he (l : Label) : (∫u : ℝ,columnDensity V hc hs u*φ l u)=
      scalar l*(Real.sqrt (T l):ℂ)⁻¹*
        commonWindow (src l) (C l) (hC l) (τ l) (t l) (θ l) (X l) V (L l) (z l) := by
    have hh := common_window_original_integral (src l) (s l).pools_ne (s l).prime
      (C l) (hC l) (hseed l) (τ l) (t l) (T l) (θ l) (X l) (hX l)
      V hc hs (L l) (z l)
    rw [mul_assoc,hh,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [φ,allocatedPolynomial]
    ring
  simpa only [he,src] using hbound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def geometryOriginalSector (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) :
    FirstSector (originalFirstBlock s R seed K Z ξ hK) := ⟨q.1.val,q.2⟩

def geometryLeftScalar (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  weight q.1.val*(geometryFirstSource s R seed K Z ξ hK key q.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
      leftExponent A (geometryExponents s R seed K Z ξ q.1.val))):ℂ)

omit [DecidableEq ι] in
/-- Specialization to the actual normalized left Hilbert energy in one
geometry group. The original outside scalar, source volume and every
first-sector coordinate are preserved through the Mellin integral. -/
theorem actual_geometry_left_window_energy (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (hseed : ∀q : CommonGeometryFiber s R seed K Z ξ key,
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).C)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 2)) (hs : ContDiff ℝ ∞ (V 2))
    (t T : ℝ) (hT : 0< T) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
        ‖geometryLeftScalar s R seed K Z ξ M A hK key weight q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            (geometryFirstSource s R seed K Z ξ hK key q.1).C q.2.1.val
            (originalFirstPair s R seed K Z ξ hK
              (geometryOriginalSector s R seed K Z ξ hK key q)).left
            (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val‖^2)≤ E*(1+‖u‖)^(2*J)) :
    geometryLeftEnergy s R seed K Z ξ M A hK key (fun q=>weight q.val) V t/T≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity (V 2) hc hs u‖)^2 := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let lift := geometryOriginalSector s R seed K Z ξ hK key
  have hh := actual_joint_first_window_energy (firstActiveSectors src V)
    (fun _ : FirstSector src=>s) (fun _=>R) (fun _=>seed)
    (fun q=>(src q.1).C) (fun q=>q.2.1.val) (fun q=>(src q.1).hC)
    (fun q=>hseed q.1)
    (fun q=>(originalFirstPair s R seed K Z ξ hK (lift q)).left)
    (fun _=>s.t) (fun _=>T) (fun _=>t) (fun q=>(src q.1).A0)
    (fun q=>(src q.1).A0_pos) (fun q=>q.2.2.2.2.val)
    (fun q=>geometryLeftScalar s R seed K Z ξ M A hK key weight q) (V 2) hc hs J E hE henergy
  apply le_trans (le_of_eq ?_) hh
  rw [geometryLeftEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  have hcol := actual_first_left_common_window s R seed K Z ξ hK weight (lift q) (V 2) t
  change CenteredMomentCauchy.leftColumn Finset.univ
    (firstJointLeft src (fun q=>weight q.val) q) (V 2) (firstLeftLog (src q.1)) t=_ at hcol
  rw [hcol]
  dsimp only [geometryLeftScalar]
  simp only [norm_mul,norm_div,norm_inv,mul_pow,div_pow,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),Real.sq_sqrt hT.le]
  dsimp [src,lift,geometryOriginalSector,geometryFirstSource]
  ring

def geometryRightScalar (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  (Real.sqrt (Z^(rightExponent A (geometryExponents s R seed K Z ξ q.1.val))):ℂ)⁻¹

omit [DecidableEq ι] in
/-- The matching right energy uses the reflected row and conjugate window;
its Mellin height is independent of the left one. -/
theorem actual_geometry_right_window_energy (s : Input ι) (R seed : Ideal O)
    (K Z ξ A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (hseed : ∀q : CommonGeometryFiber s R seed K Z ξ key,
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).D)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 3)) (hs : ContDiff ℝ ∞ (V 3))
    (t T : ℝ) (hT : 0< T) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
        ‖geometryRightScalar s R seed K Z ξ A hK key q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            (geometryFirstSource s R seed K Z ξ hK key q.1).D q.2.1.val
            (originalFirstPair s R seed K Z ξ hK
              (geometryOriginalSector s R seed K Z ξ hK key q)).right
            (s.t+2*Real.pi*(u-(-t))) T (-q.2.2.2.2.val)‖^2)≤ E*(1+‖u‖)^(2*J)) :
    geometryRightEnergy s R seed K Z ξ A hK key V t/T≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (V 3 x))
        (CenteredMomentConjugateWindow.conjugate_compact (V 3) hc)
        (CenteredMomentConjugateWindow.conjugate_smooth (V 3) hs) u‖)^2 := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let lift := geometryOriginalSector s R seed K Z ξ hK key
  have hh := actual_joint_first_window_energy (firstActiveSectors src V)
    (fun _ : FirstSector src=>s) (fun _=>R) (fun _=>seed)
    (fun q=>(src q.1).D) (fun q=>q.2.1.val) (fun q=>(src q.1).hD)
    (fun q=>hseed q.1)
    (fun q=>(originalFirstPair s R seed K Z ξ hK (lift q)).right)
    (fun _=>s.t) (fun _=>T) (fun _=>-t) (fun q=>(src q.1).B0)
    (fun q=>(src q.1).B0_pos) (fun q=>-q.2.2.2.2.val)
    (fun q=>geometryRightScalar s R seed K Z ξ A hK key q) (fun x=>star (V 3 x))
    (CenteredMomentConjugateWindow.conjugate_compact (V 3) hc)
    (CenteredMomentConjugateWindow.conjugate_smooth (V 3) hs) J E hE henergy
  apply le_trans (le_of_eq ?_) hh
  rw [geometryRightEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  have hcol := actual_first_right_common_window s R seed K Z ξ hK (lift q) (V 3) t
  change CenteredMomentCauchy.rightColumn Finset.univ
    (firstJointRight src q) (V 3) (firstRightLog (src q.1)) t=_ at hcol
  rw [hcol]
  dsimp only [geometryRightScalar]
  simp only [norm_mul,norm_inv,norm_star,mul_pow,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),Real.sq_sqrt hT.le]
  dsimp [src,lift,geometryOriginalSector,geometryFirstSource]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_first_window_energy
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_left_window_energy
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_right_window_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.JointWindowEnergy -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySources; sha256 659f7441bda50b492b57d931f21bf8902e78bc76b7ba65cf5d39ae5e81a87637 -/
section
                                                 
                                                     

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentLogDyadic
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem actual_geometry_seed (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ)) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (q : CommonGeometryFiber s R seed K Z ξ key) :
    seed∣(geometryFirstSource s R seed K Z ξ hK key q).C ∧
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).D := by
  have hh := actual_common_gates s R seed hs hz₁ hz₂ q.val.1.val.1 q.val.1.val.2 q.val.1.property
  exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩

def geometryColumnIdeal (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : Ideal O :=
  if reflected then (geometryFirstSource s R seed K Z ξ hK key j.1).D
    else (geometryFirstSource s R seed K Z ξ hK key j.1).C

def geometryColumnCharacter (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : Character :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  let pair := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  if reflected then pair.right else pair.left

def geometryColumnScalar (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  if reflected then
    (Real.sqrt (Z^(rightExponent A (geometryExponents s R seed K Z ξ j.1.val))):ℂ)⁻¹
  else weight j.1.val*(geometryFirstSource s R seed K Z ξ hK key j.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ j.1.val)+
      leftExponent A (geometryExponents s R seed K Z ξ j.1.val))):ℂ)

/-- Literal live child-source budget for one side of the first transform.
No estimate of its main, error, low or high branch is assumed here. -/
def geometryLiveBudget (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (b t : ℝ) : ℝ :=
  let src := geometryFirstSource s R seed K Z ξ hK key
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key
  let τ := geometryColumnCharacter reflected s R seed K Z ξ hK key
  ∑j∈firstLiveColumns src (fun _=>logAnnulus),
    ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
      ((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
        ∑B : actualAllocations s.pools (C j),
          if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R j.2.1.val B
              (τ j) t CenteredMomentFirstAnnularMajorant.profile (src j.1).H0
          else 0)

theorem actual_geometry_source_budget (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b t : ℝ) (ha : 0< a) (hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :
    let src := geometryFirstSource s R seed K Z ξ hK key
    let C := geometryColumnIdeal reflected s R seed K Z ξ hK key
    let τ := geometryColumnCharacter reflected s R seed K Z ξ hK key
    (∑q∈firstActiveSectors src (fun _=>logAnnulus),
      ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight (firstSectorColumn src q)*
        allocatedPolynomial (original s R seed) (C (firstSectorColumn src q)) q.2.1.val
          (τ (firstSectorColumn src q)) t (volume s) (firstSignedRow reflected q.2.2.2.2.val)‖^2)≤
      geometryLiveBudget reflected s R seed K Z ξ M A hK key weight N b t := by
  intro src C τ
  have hC (j : FirstColumnIndex src) : Supported (C j) := by
    cases reflected
    · exact (src j.1).hC
    · exact (src j.1).hD
  have hseed (j : FirstColumnIndex src) : seed∣C j := by
    have hh := actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ j.1
    cases reflected
    · exact hh.1
    · exact hh.2
  have hh := actual_active_common_live_energy reflected src N a b ha s hcard haS hbS C R seed
    hC hseed τ (fun _=>t)
    (fun j=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2)
    (fun _=>sq_nonneg _)
  simpa only [norm_mul,mul_pow,geometryLiveBudget,src,C,τ] using hh


/-- The literal left child budget supplies the source premise of the
Mellin-window theorem, with original source volume as normalization. -/
theorem actual_geometry_left_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0< a) (hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (hbudget : ∀u : ℝ, geometryLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤ E*(1+‖u‖)^(2*J)) :
    geometryLeftEnergy s R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        logAnnulus hc hsm u‖)^2 := by
  apply actual_geometry_left_window_energy s R seed K Z ξ M A hK hZ key weight
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).1)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_geometry_source_budget false s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-t)) ha hcard haS hbS hs hz₁ hz₂
  exact le_trans hh (hbudget u)

/-- The reflected right budget passes through its independent Mellin
height, retaining the conjugate window from the actual first transform. -/
theorem actual_geometry_right_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0< a) (hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (hbudget : ∀u : ℝ, geometryLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤ E*(1+‖u‖)^(2*J)) :
    geometryRightEnergy s R seed K Z ξ A hK key (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        (fun x=>star (logAnnulus x))
        (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
        (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖)^2 := by
  apply actual_geometry_right_window_energy s R seed K Z ξ A hK hZ key
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).2)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_geometry_source_budget true s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-(-t))) ha hcard haS hbS hs hz₁ hz₂
  exact le_trans hh (hbudget u)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_seed
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_source_budget

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_left_budget_window
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_right_budget_window

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySources -/
