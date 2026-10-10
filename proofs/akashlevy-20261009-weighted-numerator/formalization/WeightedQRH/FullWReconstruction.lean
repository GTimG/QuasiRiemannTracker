import WeightedQRH.FullWAggregate
import WeightedQRH.MellinReconstruction

/-! The complete numerator integral is taken before any row amplitude estimate. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace WeightedQRH.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 400000

def sourceSZWeight (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
    mellin (paperRadialFourier W0) z

def rowNumeratorIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  ∫t : ℝ,(Y:ℂ)^((1/2:ℂ)+t*I-1)*mellin W1 ((1/2:ℂ)+t*I)*
    calibratedTupleValue S hS hmax η u P hPS W Yp s ((1/2:ℂ)+t*I) z

def integratedRowValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  frequencyWeight z ⟨u.val,u.property.1⟩ *
    rowNumeratorIntegral S hS hmax η u P hPS W Yp W1 Y s z

lemma weightedRow_w_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ r : ℝ) (q : ℝ×ℝ) :
    (∫t : ℝ,weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r (q,t))=
      sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*
        integratedRowValue S hS hmax η u P hPS W Yp W1 Y ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I) := by
  unfold integratedRowValue rowNumeratorIntegral
  rw [←mul_assoc,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold weightedRowOnLines sourceMellinWeight sourceSZWeight
  norm_num only [ofReal_div,ofReal_one,ofReal_ofNat]
  ring

lemma fullW_inner_integrable (H : ℝ) (f : HeightSpace→ℂ)
    (hf : IntegrableOn f (fullWSlab H) heightMeasure) :
    IntegrableOn (fun q : ℝ×ℝ=>∫t : ℝ,f (q,t)) (szRectangle H) (volume.prod volume) := by
  have hi : Integrable f (((volume.prod volume).restrict (szRectangle H)).prod volume) := by
    simpa only [IntegrableOn,fullWSlab,heightMeasure,←Measure.prod_restrict,Measure.restrict_univ] using hf
  exact hi.integral_prod_left

lemma fullW_factored_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ r H : ℝ)
    (hf : IntegrableOn (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r)
      (fullWSlab H) heightMeasure) :
    let F := fun q : ℝ×ℝ=>sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*
      integratedRowValue S hS hmax η u P hPS W Yp W1 Y ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)
    IntegrableOn F (szRectangle H) (volume.prod volume) ∧
      (∫p in fullWSlab H,weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r p
        ∂heightMeasure) = ∫q in szRectangle H,F q ∂(volume.prod volume) := by
  constructor
  · simpa only [weightedRow_w_integral] using fullW_inner_integrable H _ hf
  · rw [fullWSlab_fubini H _ hf]
    simp_rw [weightedRow_w_integral]

def integratedDyadValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),integratedRowValue S hS hmax η u (fun i=>(P i).val)
    (fun i=>hT i _ (P i).property) W Yp W1 Y s z

theorem finiteFullW_reconstruction {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun q : ℝ×ℝ=>sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
    IntegrableOn F (szRectangle H) (volume.prod volume) ∧
      finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫q in szRectangle H,F q ∂(volume.prod volume)) := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun j=>(P j).val) (fun j=>hT j _ (P j).property) η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50)
  let g (u : FreeRow) (P : ∀i,T i) (q : ℝ×ℝ) :=
    sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedRowValue S hS hmax η u (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
        W Yp W1 Y (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : IntegrableOn (f u P) (fullWSlab H) heightMeasure := by
    have hh := fullWWeightedRow_integrable e a B H i he he' ha haTop hB hH S hS hmax hfirst
      (fun j=>(P j).val) (fun j=>hT j _ (P j).property) η u (hR u hu) (ψ u) (hbin u hu)
      W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    change Integrable ((fullWSlab H).indicator (f u P)) heightMeasure at hh
    exact (integrable_indicator_iff (fullWSlab_measurable H)).mp hh
  have hg (u : FreeRow) (hu : u∈R) (P : ∀i,T i) :
      IntegrableOn (g u P) (szRectangle H) (volume.prod volume) ∧
        (∫p in fullWSlab H,f u P p ∂heightMeasure)=∫q in szRectangle H,g u P q ∂(volume.prod volume) := by
    have hh := fullW_factored_integral S hS hmax η u (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
      W Yp W0 W1 X Y Z (a+16*e) (17/50) H (hi u hu P)
    simpa only [g,f,ofReal_div,ofReal_ofNat] using hh
  have hgi (u : FreeRow) (hu : u∈R) :
      IntegrableOn (fun q=>∑P:(∀i,T i),g u P q) (szRectangle H) (volume.prod volume) :=
    integrable_finsetSum _ (fun P _=>(hg u hu P).1)
  have hF : (fun q : ℝ×ℝ=>sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I))=
      (fun q=>∑u∈R,∑P:(∀i,T i),g u P q) := by
    funext q
    simp only [integratedDyadValue,Finset.mul_sum,g]
  dsimp only
  rw [hF]
  refine ⟨integrable_finsetSum _ hgi,?_⟩
  rw [integral_finsetSum R hgi,Finset.mul_sum]
  unfold finiteCentralFullWRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>(hg u hu P).1),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [←(hg u hu P).2]
  have hh := fullWWeightedRow_integral S hS hmax (fun j=>(P j).val)
    (fun j=>hT j _ (P j).property) η u W Yp W0 W1 X Y Z a e H
  rw [show (∫p,fullWWeightedRow S hS hmax (fun j=>(P j).val)
      (fun j=>hT j _ (P j).property) η u W Yp W0 W1 X Y Z a e H p ∂heightMeasure)=
      ∫p in fullWSlab H,f u P p ∂heightMeasure by
        exact integral_indicator (fullWSlab_measurable H)] at hh
  exact hh.symm

end WeightedQRH.FullWContour
end
