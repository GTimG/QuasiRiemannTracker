/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B135
import Submissions.cycle61_c0125139.Bundles.B146
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DivisorBoundary

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.LowOneSidedHarmonic; sha256 ed4472afad112528762db859cb4e200e5d2431d3df852ebdba526e55d67d7d05 -/
section
                                                             

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass.LowOneSided
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentCommonHarmonicMass CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentWholeDivisorShell
local notation "O" => ActualEisensteinCubic.O

/-- One-sided reciprocal weight for the two separate joint Cauchy energies. -/
def sideWeight (second : Bool) (v : Label) : ℝ :=
  1/((if second then v.1.2 else v.1.1).absNorm:ℝ)

lemma one_sided_shell_scalar (e Y x y d : ℝ) (he : 0< e) (hx : 0< x) (hy : 0< y)
    (hd : 0< d) (hmin : min x y≤ d) (hY : min x y≤ Y) :
    (2*min x y)^(1+e)/d≤2^(1+e)*Y^e := by
  have hm : 0< min x y := lt_min hx hy
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  apply (div_le_iff₀ hd).mpr
  calc
    _≤2^(1+e)*(d*Y^e) := mul_le_mul_of_nonneg_left
      (mul_le_mul hmin hp (by positivity) hd.le) (by positivity)
    _=_ := by ring

/-- The same Rankin shell count used by the symmetric harmonic estimate
also controls either reciprocal norm separately. -/
theorem one_sided_shell_bound (e : ℝ) (he : 0< e) :
    ∃C : ℝ,0< C ∧ ∀second : Bool, ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0< T₁ → 0< T₂ → min T₁ T₂≤ Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Y ∧ (v.1.2.absNorm:ℝ)≤ Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,sideWeight second v)≤ C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro second s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0< Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  let d := if second then T₂ else T₁
  have hsq : 0< d := by cases second <;> assumption
  have hmin : min T₁ T₂≤ d := by
    cases second
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/d := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      cases second
      · exact (hshell v hv).1
      · exact (hshell v hv).2.2.1
    _ = (S.card:ℝ)/d := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/d :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/d) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (one_sided_shell_scalar e Y T₁ T₂ d he hT₁ hT₂ hsq hmin hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

theorem one_sided_polynomial_cap_log_bound (B e : ℝ) (hB : 0≤ B) (he : 0< e) :
    ∃C : ℝ,0< C ∧ ∀second : Bool, ∀Z : ℝ,1≤ Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑v∈S,sideWeight second v)≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := one_sided_shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0< K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro second Z hZ s hs hs0 S hS hN
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,sideWeight second v)≤ C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤ Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound second s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

theorem one_sided_harmonic_mass (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀second : Bool, ∀Z : ℝ,2≤ Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑v∈S,sideWeight second v)≤ C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0< e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := one_sided_polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro second Z hZ s hs hs0 S hS hN
  have hz : 0< Z := by linarith
  have hZ1 : 1≤ Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound second Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end
end OAI.SevenEighths.Cycle61InitialMass.LowOneSided
#print axioms OAI.SevenEighths.Cycle61InitialMass.LowOneSided.one_sided_shell_scalar
#print axioms OAI.SevenEighths.Cycle61InitialMass.LowOneSided.one_sided_shell_bound
#print axioms OAI.SevenEighths.Cycle61InitialMass.LowOneSided.one_sided_polynomial_cap_log_bound
#print axioms OAI.SevenEighths.Cycle61InitialMass.LowOneSided.one_sided_harmonic_mass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.LowOneSidedHarmonic -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowReciprocal; sha256 55fbea6a1325b03d04fd09b67b3552c1ddd2af934c82330cff40837687501bd8 -/
section
                                                      
                                                       
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentDivisorBoundary Cycle61Moment
local notation "O" => HeckeFamily.O

/-- One-sided reciprocal mass of actual equal-support labels, including their inactive
subsets. The seed saving is retained for the first-projector shell. -/
theorem actual_low_label_reciprocal_mass (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀second : Bool, ∀Z : ℝ,2≤ Z → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∑l∈labels,1/((if second then l.1.2 else l.1.1).absNorm:ℝ))≤ C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := LowOneSided.one_sided_harmonic_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro second Z hZ seed hs hs0 labels hsup heq hseed hnorm
  have hh := hbound second Z hZ seed hs hs0 (labels.image firstPartitionCode) ?_ ?_
  · rw [Finset.sum_image] at hh
    · exact hh
    · exact first_partition_code_injective.injOn
  · intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨(hsup l hl).1.1,(hsup l hl).2.1,heq l hl,(hseed l hl).1,(hseed l hl).2,?_⟩
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    rw [commonRadical_support]
    exact Q.property
  · intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    exact hnorm l hl

/-- The one-sided seed saving pays the entire first-projector dyad. No
condition that this projector divides an encoded row is used here. -/
theorem actual_low_reciprocal_projector_shell (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀second : Bool, ∀Z T : ℝ,2≤ Z → 1≤ T → ∀Ds : Finset (Ideal O),
      (∀D∈Ds,Squarefree D) →
      (∀D∈Ds,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀labels : Ideal O→ Finset FirstSourceLabel,
      (∀D∈Ds,∀l∈labels D,Supported l.1.1 ∧ Supported l.1.2) →
      (∀D∈Ds,∀l∈labels D,primeSupport l.1.1=primeSupport l.1.2) →
      (∀D∈Ds,∀l∈labels D,D∣l.1.1 ∧ D∣l.1.2) →
      (∀D∈Ds,∀l∈labels D,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∑D∈Ds,∑l∈labels D,1/((if second then l.1.2 else l.1.1).absNorm:ℝ))≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := actual_low_label_reciprocal_mass B ε hB hε
  refine ⟨256*C,by positivity,?_⟩
  intro second Z T hZ hT Ds hDs hdyad labels hsup heq hseed hnorm
  have hT0 : 0< T := zero_lt_one.trans_le hT
  have hcard := divisor_dyad_card Ds T hT (fun D hD=>(hDs D hD).ne_zero)
    (fun D hD=>(hdyad D hD).2)
  calc
    _≤∑_D∈Ds,C*Z^ε/T := by
      apply Finset.sum_le_sum
      intro D hD
      exact (hbound second Z hZ D (hDs D hD) (hDs D hD).ne_zero (labels D)
        (hsup D hD) (heq D hD) (hseed D hD) (hnorm D hD)).trans
        (div_le_div_of_nonneg_left (by positivity) hT0 (hdyad D hD).1)
    _=(Ds.card:ℝ)*(C*Z^ε/T) := by simp
    _≤(256*T)*(C*Z^ε/T) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _=(256*C)*Z^ε := by field_simp

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_label_reciprocal_mass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_reciprocal_projector_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowReciprocal -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowLabelBudget; sha256 97fd03047f55a73aaede494267b2b268beb47020841f92eba8d0c76f99811b20 -/
section
                                                    
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle61Moment Cycle61FinalCapacity
local notation "O" => HeckeFamily.O

def lowGeometryExponent (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) : ℝ :=
  A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)

/-- The exact low payment leaves a one-sided reciprocal ideal norm, which
can be summed inside each of the two separate joint Cauchy energies. -/
theorem actual_low_scalar_reciprocal (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve error : ℝ)(hZ : 1< Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error)=
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then D₂ else C₂).absNorm:ℝ) := by
  have hh := actual_low_scalar_payment reflected second l hC hD heq C₂ D₂ hC₂ U
    Z M A a ξ reserve error hZ
  dsimp only at hh ⊢
  rw [hh]
  have hn : (0:ℝ)<(if second then D₂ else C₂).absNorm := by
    cases second
    · exact CenteredMomentFirstScale.norm_pos C₂ hC₂.1
    · exact CenteredMomentFirstScale.norm_pos D₂ hD₂.1
  rw [show (A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
      Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)-
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)+error)=
      (lowGeometryExponent reflected Z A l+error)-
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) by unfold lowGeometryExponent; ring]
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn]

/-- Sum the one-sided low weights over second labels and the first
projector shell, then pay the first-label count once. -/
theorem actual_low_full_label_budget (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀(reflected second : Bool)(Z T A p exponent error : ℝ),
      2≤ Z → 1≤ T → p≤ B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z A l≤ exponent) →
      ∀(Ds : FirstSourceLabel→ Finset (Ideal O))
        (children : FirstSourceLabel→ Ideal O→ Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑l∈labels,∑D∈Ds l,∑v∈children l D,
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
          K*Z^(p+exponent+error+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨Kf,hKf,hfirst⟩ := actual_first_low_label_count B (ε/2) hB (half_pos hε)
  obtain ⟨Ks,hKs,hsecond⟩ := actual_low_reciprocal_projector_shell B (ε/2) hB (half_pos hε)
  refine ⟨Kf*Ks,mul_pos hKf hKs,?_⟩
  intro reflected second Z T A p exponent error hZ hT hp seed hs hs0 labels
    hsup heq hseed hnorm hrad hgeom Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hZ1 : 1≤ Z := by linarith
  have hZ0 : 0< Z := by linarith
  have hc := hfirst Z hZ1 p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpoint (l : FirstSourceLabel)(hl : l∈labels) :
      (∑D∈Ds l,∑v∈children l D,
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
        Z^(exponent+error)*(Ks*Z^(ε/2)) := by
    have hh := hsecond second Z T hZ hT (Ds l) (hDs l hl) (hdyad l hl) (children l)
      (hsup₂ l hl) (heq₂ l hl) (hseed₂ l hl) (hnorm₂ l hl)
    calc
      _=Z^(lowGeometryExponent reflected Z A l+error)*
          (∑D∈Ds l,∑v∈children l D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
        simp only [Finset.mul_sum,mul_one_div]
      _≤ Z^(exponent+error)*(Ks*Z^(ε/2)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [hgeom l hl])) hh
        (by positivity) (by positivity)
  calc
    _≤∑_l∈labels,Z^(exponent+error)*(Ks*Z^(ε/2)) := Finset.sum_le_sum hpoint
    _=(labels.card:ℝ)*(Z^(exponent+error)*(Ks*Z^(ε/2))) := by simp
    _≤(Kf*Z^(p+ε/2)/(seed.absNorm:ℝ))*(Z^(exponent+error)*(Ks*Z^(ε/2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by
      have hsplit : Z^ε=Z^(ε/2)*Z^(ε/2) := by
        rw [←Real.rpow_add hZ0,add_halves]
      simp only [Real.rpow_add hZ0]
      rw [hsplit]
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_scalar_reciprocal
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_full_label_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowLabelBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondChildLowPayment; sha256 918873972ccbc4083abf8bc748ceb58ab47cdb4bea2288a168bbdddaa16bc2d0 -/
section
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Low scalar payment for the literal first common child. The remaining
weight is the one-sided reciprocal norm used by the low label budget. -/
theorem eventual_actual_child_low_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(M a ξ reserve error : ℝ),
    let A := Real.logb Z (volume s)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume (child s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error) ≤
      Z^(lowGeometryExponent reflected Z A l+error+εv)/((if second then D₂ else C₂).absNorm:ℝ) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq Rfirst B χ t hB C₂ D₂ hC₂ hD₂ U M a ξ reserve error
  let A := Real.logb Z (volume s)
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hZ := zero_lt_one.trans hz.1
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s := Real.rpow_logb hZ hz.1.ne' (volume_pos s)
  have hratio : ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)/volume s=
      (Z^(A-c))⁻¹ := by
    rw [Real.rpow_sub hZ,hV,Real.rpow_logb hZ hz.1.ne' hc,inv_div]
  have hi := hz.2 s hcard hlow _ Rfirst B χ t hB
  rw [hratio] at hi
  have hmain : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t) ≤
      Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c)) := by
    have hh := mul_le_mul_of_nonneg_left hi
      (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ l).le
    simpa only [div_eq_mul_inv,mul_left_comm] using hh
  have hp := actual_low_scalar_reciprocal reflected second l hC hD heq C₂ D₂ hC₂ hD₂ U
    Z M A a ξ reserve error hz.1
  dsimp only at hp ⊢
  rw [hV] at hp
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hZ (-a)).le)
      (div_nonneg (normalizer_pos C₂ D₂ hC₂ U).le (Real.rpow_nonneg hZ.le (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))))
    (Real.rpow_nonneg hZ.le (Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error))
  apply hh.trans_eq
  rw [show Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c))=
    (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c))*Z^εv by ring]
  calc
    _=Z^εv*(Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^(Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))*
      Z^(Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error)) := by ring
    _=_ := by rw [hp,←mul_div_assoc,←Real.rpow_add hZ]; congr 2 <;> ring

/-- Include the common-allocation small-power cost while retaining the
reciprocal norm required by the one-sided Rankin estimate. -/
theorem eventual_actual_child_low_mass_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(M a ξ reserve error εcommon Bnorm : ℝ),0≤εcommon →
    ((if second then D₂ else C₂).absNorm:ℝ)≤ Z^Bnorm →
    let A := Real.logb Z (volume s)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume (child s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U*((if second then D₂ else C₂).absNorm:ℝ)^(εcommon-1))*Z^(nominal+a+error) ≤
      Z^(lowGeometryExponent reflected Z A l+error+εv+Bnorm*εcommon)/((if second then D₂ else C₂).absNorm:ℝ) := by
  filter_upwards [eventual_actual_child_low_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ hD₂ U M a ξ reserve error εcommon Bnorm hecommon hnorm
  have hh := hz.2 s hcard hlow reflected second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ hD₂ U M a ξ reserve error
  have hzpos : 0< Z := zero_lt_one.trans hz.1
  let n : ℝ := (if second then D₂ else C₂).absNorm
  have hn : 0< n := by
    cases second
    · exact norm_pos C₂ hC₂.1
    · exact norm_pos D₂ hD₂.1
  have hncap : n^εcommon≤ Z^(Bnorm*εcommon) :=
    (Real.rpow_le_rpow hn.le hnorm hecommon).trans_eq (Real.rpow_mul hzpos.le _ _).symm
  have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hn.le εcommon)
  dsimp only at hp ⊢
  have heqpow : Z^(Real.logb Z n)=n := Real.rpow_logb hzpos hz.1.ne' hn
  have heqleft : normalizer C₂ D₂ U*n^(εcommon-1)=
      (normalizer C₂ D₂ U/Z^(Real.logb Z n))*n^εcommon := by
    rw [Real.rpow_sub hn,Real.rpow_one,heqpow]
    ring
  change Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U*n^(εcommon-1))*
      Z^(Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error)≤ _
  rw [heqleft]
  have hupper := mul_le_mul_of_nonneg_left hncap
    (div_nonneg (Real.rpow_nonneg hzpos.le
      (lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+error+εv)) hn.le)
  apply le_trans _ (hupper.trans_eq ?_)
  · convert hp using 1 <;> dsimp only [n] <;> ring
  · rw [div_mul_eq_mul_div,←Real.rpow_add hzpos]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_low_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_low_mass_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondChildLowPayment -/
