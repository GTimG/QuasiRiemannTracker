/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B025
import Submissions.certb_local_20261013.Bundles.B030
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Endpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad

/- BEGIN ORIGINAL MODULE Global.Numerator.Scalar.Exponent ; sha256 58c7f36c6d98b651247faa6b68700c84a1379f4bad04d534d65214bd9fd977ac -/
section



noncomputable section
namespace Submission20261012.Global.Numerator.Scalar
open Cycle25.Numerator.Scalar
def numeratorExponent (kap d delta p : ℝ) : ℝ :=
  -ly/2+ell*(17/50-1/2)+delta*p*ell+
    d*((3*OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap+1)/4-17/50)-
      delta*p*(2*ly-d)/(12*kap)

def weightedSourceSZExponent (a e : ℝ) : ℝ :=
  lx*(1/2-17/50)+a+16*e+17/50-1


def localNumeratorExponent (kap d delta p : ℝ) : ℝ :=
  -ly/2+ell*(17/50-1/2)+delta*p*ell+
    d*((3*OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap+1)/4-17/50)-
      delta*p*(2*ly-d+(429/100000)*d)/9

def piecewiseNumeratorExponent (kap d delta p : ℝ) : ℝ :=
  if Endpoint.junction ≤ d then localNumeratorExponent kap d delta p
    else numeratorExponent kap d delta p

theorem physical_exponent_identity (kap d delta p : ℝ)
    (hk : 7/10 ≤ kap) (hd : (1/2:ℝ) ≤ d) :
    piecewiseNumeratorExponent kap d delta p+
      weightedSourceSZExponent ((1+delta)/2) 0 =
      Endpoint.sourcePiecewiseRowExponent kap d delta p-(4+b)/6 := by
  have hy : Endpoint.y ≤ d := (show Endpoint.y < (1:ℝ)/2 by
    norm_num [Endpoint.y,Endpoint.h,Endpoint.ell]).le.trans hd
  have hm : min d (2*Endpoint.y-d)=2*Endpoint.y-d := min_eq_right (by linarith)
  unfold piecewiseNumeratorExponent Endpoint.sourcePiecewiseRowExponent
  split_ifs <;> simp only [numeratorExponent, localNumeratorExponent, weightedSourceSZExponent,
    Endpoint.sourceGlobalRowExponent, Endpoint.sourceLocalRowExponent]
  all_goals
    simp only [rowCount_binding hk,hm]
    norm_num [ly,lx,ell,h,b,Endpoint.y,Endpoint.x,Endpoint.h,Endpoint.ell]
    ring

theorem source_numerator_feedback {beta d delta p : ℝ}
    (hbeta : theta < beta) (hd : (1/2:ℝ) ≤ d) (hdtop : d ≤ h+rowExtension)
    (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    piecewiseNumeratorExponent (2*beta-1) d delta p+
      weightedSourceSZExponent ((1+delta)/2) 0 ≤
      signal beta-1/100000000-(3/4)*(beta-theta) := by
  have hk : (7:ℝ)/10 ≤ 2*beta-1 := by
    have ht : (7:ℝ)/10 < 2*theta-1 := by norm_num [theta,Endpoint.theta]
    linarith
  have hb := Endpoint.source_beta_feedback beta d delta p hbeta.le
    (show Endpoint.dmin ≤ d by norm_num [Endpoint.dmin];linarith)
    hdtop hdelta.1 hdelta.2 hp.1 hp.2
  rw [physical_exponent_identity _ _ _ _ hk hd]
  unfold signal
  change Endpoint.sourcePiecewiseRowExponent (2*beta-1) d delta p-beta ≤
    -1/100000000-(3/4)*(beta-theta) at hb
  linarith

end Submission20261012.Global.Numerator.Scalar
#print axioms Submission20261012.Global.Numerator.Scalar.physical_exponent_identity
#print axioms Submission20261012.Global.Numerator.Scalar.source_numerator_feedback
end
/- END ORIGINAL MODULE Global.Numerator.Scalar.Exponent -/

/- BEGIN ORIGINAL MODULE Global.Transport.CentralFiniteError ; sha256 84a4ace2ab3a471a04481e85f936c679cd1c4bb0ec0c4c1b4fb0db26ef34e94b -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
variable {ι : Type*} [Fintype ι]

lemma central_prime_tuple_count {K : ℕ} (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(Submission20261012.Global.ell:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(Submission20261012.Global.ell:ℝ) := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CentralFiniteError -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeErrorSaving ; sha256 79fe177329df41460b9585adaf5d9c4a8ddc79ad797035d30b18615e850c4cc6 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0 < b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0 < e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((Submission20261012.Global.h:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(Submission20261012.Global.ell:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2 < B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*Submission20261012.Global.ell)+saving)/τ)
  have hN' : (8+3*Submission20261012.Global.ell)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(8+3*Submission20261012.Global.ell)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Submission20261012.Global.ell))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*Submission20261012.Global.ell)/height H^N) := by
      have hh : Z^(6+3*Submission20261012.Global.ell)*Z^(2:ℝ)=Z^(8+3*Submission20261012.Global.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*Submission20261012.Global.ell)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CubeErrorSaving -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeSlotExponent ; sha256 fddf15b5f82088a373f10fd9c3328efedfad9411880f654c917832f1e1ea8914 -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/





/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=Submission20261012.Global.ell) :
    (∑j∈slots,ell j/d)=Submission20261012.Global.ell/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=Submission20261012.Global.ell) :
    weightedMean slots (fun j=> ell j/d) g= (1/Submission20261012.Global.ell)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0< Z) (hd : d≠0) (hell : ∑j∈slots,ell j=Submission20261012.Global.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(Submission20261012.Global.ell*(4/25))+weightedMean slots (fun j=> ell j/d) g*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp [Submission20261012.Global.ell_pos.ne']

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤ Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CubeSlotExponent -/

/- BEGIN ORIGINAL MODULE Global.Transport.EasyExponent ; sha256 06b0b61c546337fbe74439e68a36697c1e9627a4a4983dd3829e62339a9f6274 -/
section
/- Rational Bernstein certificate adapted from WeightedQRH upstream PR6. Coefficients below are checked by Lean ring arithmetic. -/



noncomputable section
namespace Submission20261012.Global.Transport
lemma tight_geometry : (793999:ℝ)/1000000 < h ∧ h < 7940001/10000000 ∧ (45959:ℝ)/100000 < ly := by
  norm_num [h,ly,Endpoint.h,Endpoint.y,Endpoint.ell]

def oldCount (delta x : ℝ) := OAI.SevenEighths.Endpoint.balancedRowCount delta (1/2-x)
def countD (x : ℝ) : ℝ := 3-17/9*x
def countP (x : ℝ) : ℝ := (2-8/9*x)*(1-x)
def countDen (delta x : ℝ) : ℝ := (5/6-delta)*countD x+delta*countP x
def countNum (delta x : ℝ) : ℝ := (1-delta)*countDen delta x+(5/6-delta)*delta*countP x/2
lemma countDen_pos {delta x : ℝ} (hd : 0≤ delta) (hd1 : delta≤3/4) (_hx : 0≤ x) (hx1 : x≤1/2) : 0< countDen delta x := by
  have ha : 0<5/6-delta := by linarith
  have hb : 0< countD x := by dsimp [countD];linarith
  have hc : 0≤ countP x := by dsimp [countP];apply mul_nonneg <;> linarith
  exact add_pos_of_pos_of_nonneg (mul_pos ha hb) (mul_nonneg hd hc)
lemma oldCount_formula {delta x : ℝ} (hj : countDen delta x≠0) : oldCount delta x=countNum delta x/countDen delta x := by
  have hd : OAI.SevenEighths.Endpoint.balanceDenominator delta (1/2-x)=countDen delta x := by
    unfold OAI.SevenEighths.Endpoint.balanceDenominator OAI.SevenEighths.Endpoint.denominator OAI.SevenEighths.Endpoint.primeWeight countDen countD countP
    ring
  unfold oldCount OAI.SevenEighths.Endpoint.balancedRowCount OAI.SevenEighths.Endpoint.balancedCutoff
  rw [hd]
  unfold countNum countP
  simp only [OAI.SevenEighths.Endpoint.primeWeight]
  field_simp
  ring

def conservativeRest (delta x : ℝ) : ℝ :=
  (1+delta)*(1-(45959 / 100000 : ℝ))/2-(167200 / 1000000 : ℝ)/2+delta*x*(167201 / 1000000 : ℝ)+(794001 / 1000000 : ℝ)*(delta/2-1/6)-(10935831 / 12500000 : ℝ)

def conservativeCert (delta x : ℝ) : ℝ :=
  -((conservativeRest delta x+1/2000)*countDen delta x+(794001/1000000)*countNum delta x)
lemma conservativeCert_identity (delta x : ℝ) : conservativeCert delta x =
  (11742291 / 2500000 : ℝ)*delta^0*(1/3-delta)^2*x^0*(1/2-x)^3
  + (37836271 / 3000000 : ℝ)*delta^0*(1/3-delta)^2*x^1*(1/2-x)^2
  + (2609398 / 234375 : ℝ)*delta^0*(1/3-delta)^2*x^2*(1/2-x)^1
  + (48273863 / 15000000 : ℝ)*delta^0*(1/3-delta)^2*x^3*(1/2-x)^0
  + (6191091 / 12500000 : ℝ)*delta^1*(1/3-delta)^1*x^0*(1/2-x)^3
  + (511484303 / 225000000 : ℝ)*delta^1*(1/3-delta)^1*x^1*(1/2-x)^2
  + (75362677 / 25000000 : ℝ)*delta^1*(1/3-delta)^1*x^2*(1/2-x)^1
  + (69554857 / 56250000 : ℝ)*delta^1*(1/3-delta)^1*x^3*(1/2-x)^0
  + (7100093 / 6250000 : ℝ)*delta^2*(1/3-delta)^0*x^0*(1/2-x)^3
  + (17552333 / 14062500 : ℝ)*delta^2*(1/3-delta)^0*x^1*(1/2-x)^2
  + (69237863 / 225000000 : ℝ)*delta^2*(1/3-delta)^0*x^2*(1/2-x)^1
  + (10563683 / 225000000 : ℝ)*delta^2*(1/3-delta)^0*x^3*(1/2-x)^0
    := by
  unfold conservativeCert conservativeRest countNum countDen countD countP
  ring
lemma conservativeCert_nonneg {delta x : ℝ} (hd : 0≤ delta) (hd1 : delta≤1/3) (hx : 0≤ x) (hx1 : x≤1/2) : 0≤ conservativeCert delta x := by
  rw [conservativeCert_identity]
  have ha : 0≤1/3-delta := by linarith
  have hb : 0≤1/2-x := by linarith
  positivity
lemma oldCount_bounds {delta x : ℝ} (hd : 0≤ delta) (hd1 : delta≤3/4) (hx : 0≤ x) (hx1 : x≤1/2) :
    1-delta≤ oldCount delta x ∧ oldCount delta x≤1-2*delta/3 := by
  have hj := countDen_pos hd hd1 hx hx1
  have ha : 0≤5/6-delta := by linarith
  have hp : 0≤ countP x := by unfold countP;apply mul_nonneg <;> linarith
  have hdp : 0≤2*countD x-3*countP x := by
    unfold countD countP
    nlinarith [mul_nonneg hx (show 0≤1/2-x by linarith)]
  have hn := mul_nonneg (mul_nonneg ha hd) hp
  have hprod := mul_nonneg hd (add_nonneg (mul_nonneg ha hdp) (mul_nonneg (by linarith : 0≤2*delta) hp))
  rw [oldCount_formula hj.ne']
  constructor
  · apply (le_div_iff₀ hj).2
    unfold countNum
    linarith
  · apply (div_le_iff₀ hj).2
    unfold countNum countDen at *
    nlinarith

def genericOldExponent (d delta q R : ℝ) : ℝ :=
  (1+delta)/2-theta+h*(17/50-1/6)-(1+delta)/2*ly-ell/2+q*ell+d*(R+delta/2-17/50)
def OriginalBranch (d a : ℝ) : Prop := d≤ h+rowExtension ∧ (2*a-1≤1/3 ∨ d≤1/2)

lemma low_delta_bound {d delta x : ℝ} (_hd : 0≤ d) (hd1 : d≤ h+rowExtension)
    (hdelta : 0≤ delta) (hdelta1 : delta≤1/3) (hx : 0≤ x) (hx1 : x≤1/2) :
    genericOldExponent d delta (delta*x) (oldCount delta x)≤-1/2000 := by
  have hr := oldCount_bounds hdelta (by linarith) hx hx1
  have hj := countDen_pos hdelta (by linarith) hx hx1
  have hc := conservativeCert_nonneg hdelta hdelta1 hx hx1
  have he : conservativeRest delta x+(794001/1000000)*oldCount delta x≤-1/2000 := by
    rw [oldCount_formula hj.ne']
    have hi : conservativeCert delta x = -countDen delta x*(conservativeRest delta x+(794001/1000000)*(countNum delta x/countDen delta x)+1/2000) := by
      unfold conservativeCert
      field_simp
      ring
    rw [hi] at hc
    nlinarith [hj]
  have hh := tight_geometry
  have hdy : d≤794001/1000000 := by norm_num [rowExtension, Endpoint.zeta] at hd1;linarith
  have hs : 0≤ oldCount delta x+delta/2-17/50 := by linarith [hr.1]
  have hm := mul_le_mul_of_nonneg_right hdy hs
  have ht : 10935831/12500000≤ theta := by norm_num [theta, Endpoint.theta]
  have hly := mul_le_mul_of_nonneg_left hh.2.2.le (show 0≤(1+delta)/2 by positivity)
  have hq := mul_le_mul_of_nonneg_left ell_interval.2.le (mul_nonneg hdelta hx)
  have hfreq := mul_le_mul_of_nonneg_right hh.2.1.le (by norm_num : (0:ℝ)≤17/50-1/6)
  unfold genericOldExponent conservativeRest at *
  nlinarith [ell_interval.1]

lemma intermediate_bound {d delta q : ℝ} (hd : 0≤ d) (hd1 : d≤1/2)
    (hdelta : 0≤ delta) (hdelta1 : delta≤3/4) (hq : 0≤ q) (hq1 : q≤ delta/2) :
    genericOldExponent d delta q (oldCount delta (q/delta))≤-1/2000 := by
  by_cases hz : delta=0
  · subst delta
    have hqz : q=0 := by linarith
    subst q
    have hr := oldCount_bounds (delta:=0) (x:=0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hr.2 hd
    unfold genericOldExponent
    rw [show (0:ℝ)/0=0 by simp] at *
    rw [theta_eq]
    nlinarith [tight_geometry,ell_interval.1,ell_interval.2]
  have hp : 0< delta := lt_of_le_of_ne hdelta (Ne.symm hz)
  have hx : 0≤ q/delta := div_nonneg hq hp.le
  have hx1 : q/delta≤1/2 := (div_le_iff₀ hp).2 (by linarith)
  have hr := oldCount_bounds hdelta hdelta1 hx hx1
  have hm := mul_le_mul_of_nonneg_left hr.2 hd
  have hs : 0≤1-2*delta/3+delta/2-17/50 := by linarith
  have hm1 := mul_le_mul_of_nonneg_right hd1 hs
  have hqell := mul_le_mul_of_nonneg_right hq1 ell_pos.le
  have hly := mul_le_mul_of_nonneg_left tight_geometry.2.2.le (show 0≤(1+delta)/2 by positivity)
  have hfreq := mul_le_mul_of_nonneg_right tight_geometry.2.1.le (by norm_num : (0:ℝ)≤17/50-1/6)
  unfold genericOldExponent
  rw [theta_eq]
  have hdel := mul_le_mul_of_nonneg_left ell_interval.2.le hdelta
  nlinarith [ell_interval.1,ell_interval.2]

lemma original_branch_exponent {d a q : ℝ} (hd : 0≤ d) (ha : 51/100< a) (ha1 : a≤7/8)
    (hq : 0≤ q) (hq1 : q≤(2*a-1)/2) (hb : OriginalBranch d a) :
    genericOldExponent d (2*a-1) q (oldCount (2*a-1) (q/(2*a-1)))≤-1/2000 := by
  have hp : 0<2*a-1 := by linarith
  rcases hb with ⟨ht,hb|hb⟩
  · have hh := low_delta_bound hd ht hp.le hb (div_nonneg hq hp.le) ((div_le_iff₀ hp).2 (by linarith))
    simpa only [mul_div_cancel₀ q hp.ne'] using hh
  · exact intermediate_bound hd hb hp.le (by linarith) hq hq1
end Submission20261012.Global.Transport

#print axioms Submission20261012.Global.Transport.original_branch_exponent
end
/- END ORIGINAL MODULE Global.Transport.EasyExponent -/

/- BEGIN ORIGINAL MODULE Global.Transport.FloorExponent ; sha256 e7f9ec8d1a8546e3ec8f1ad1754440934c1d49589496716bfaa7f40ca534d357 -/
section


noncomputable section
namespace Submission20261012.Global.Transport
def centralScale (a e : ℝ) : ℝ := lx*(4/25)+(a+16*e-33/50)+ly*(-a-6*e)
lemma physical_scale_identity (Z a e : ℝ) (hZ : 0< Z) :
    (Z^lx)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^ly)^(-a-6*e)=Z^(centralScale a e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ, ←Real.rpow_add hZ]
  rfl
def floorSourceExponent (v : ℝ) : ℝ := centralScale (51/100) 0+v*(67/100)-3*ell/20
def floorRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*ly)*e+v*(12*e+eps*(N+8))+loss+mesh*ell
lemma floor_source_margin {v : ℝ} (hv : v≤ h+rowExtension) :
    floorSourceExponent v≤ signal theta-1/100 := by
  norm_num [floorSourceExponent, centralScale, signal, b, rowExtension, h, lx, ly, ell,
    theta, Endpoint.theta, Endpoint.ell, Endpoint.h, Endpoint.x, Endpoint.y, Endpoint.zeta] at hv ⊢
  linarith

lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤ e) (heps : 0≤ eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [Submission20261012.Global.ly_coarse, mul_nonneg he (by linarith [Submission20261012.Global.ly_coarse] : 0≤ ly-1/3)]
end Submission20261012.Global.Transport

#print axioms Submission20261012.Global.Transport.floor_source_margin
end
/- END ORIGINAL MODULE Global.Transport.FloorExponent -/
