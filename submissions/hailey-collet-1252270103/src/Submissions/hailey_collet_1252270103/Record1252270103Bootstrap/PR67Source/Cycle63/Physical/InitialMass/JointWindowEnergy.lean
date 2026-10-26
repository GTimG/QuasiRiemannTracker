import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.JointBlock
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryContraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy FourierBridge
local notation "O" => HeckeFamily.O

lemma finite_set_weighted_integral_energy {κ : Type*} (S : Finset κ)
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (w : ℝ→ℝ) (hw : ∀t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t=>w t*‖b t‖))
    (hφ : ∀k,Integrable (fun t=>b t*φ k t))
    (hbound : ∀t,(∑k∈S,‖φ k t‖^2)≤E*(w t)^2) :
    (∑k∈S,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,w t*‖b t‖)^2 := by
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
    (hX : ∀l,0<X l) (z : Label→O) (scalar : Label→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤E)
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
  have hb (u : ℝ) : (∑l∈labels,‖φ l u‖^2)≤E*((1+‖u‖)^J)^2 := by
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

def geometryOriginalSector (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) :
    FirstSector (originalFirstBlock s R seed K Z ξ hK) := ⟨q.1.val,q.2⟩

def geometryLeftScalar (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  weight q.1.val*(geometryFirstSource s R seed K Z ξ hK key q.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
      leftExponent A (geometryExponents s R seed K Z ξ q.1.val))):ℂ)

omit [DecidableEq ι] in
/-- Specialization to the actual normalized left Hilbert energy in one
geometry group. The original outside scalar, source volume and every
first-sector coordinate are preserved through the Mellin integral. -/
theorem actual_geometry_left_window_energy (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (hseed : ∀q : CommonGeometryFiber s R seed K Z ξ key,
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).C)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 2)) (hs : ContDiff ℝ ∞ (V 2))
    (t T : ℝ) (hT : 0<T) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
        ‖geometryLeftScalar s R seed K Z ξ M A hK key weight q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            (geometryFirstSource s R seed K Z ξ hK key q.1).C q.2.1.val
            (originalFirstPair s R seed K Z ξ hK
              (geometryOriginalSector s R seed K Z ξ hK key q)).left
            (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val‖^2)≤E*(1+‖u‖)^(2*J)) :
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
  refine Finset.sum_congr rfl fun q hq => ?_
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

def geometryRightScalar (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  (Real.sqrt (Z^(rightExponent A (geometryExponents s R seed K Z ξ q.1.val))):ℂ)⁻¹

omit [DecidableEq ι] in
/-- The matching right energy uses the reflected row and conjugate window;
its Mellin height is independent of the left one. -/
theorem actual_geometry_right_window_energy (s : Input ι) (R seed : Ideal O)
    (K Z ξ A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (hseed : ∀q : CommonGeometryFiber s R seed K Z ξ key,
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).D)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 3)) (hs : ContDiff ℝ ∞ (V 3))
    (t T : ℝ) (hT : 0<T) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
        ‖geometryRightScalar s R seed K Z ξ A hK key q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            (geometryFirstSource s R seed K Z ξ hK key q.1).D q.2.1.val
            (originalFirstPair s R seed K Z ξ hK
              (geometryOriginalSector s R seed K Z ξ hK key q)).right
            (s.t+2*Real.pi*(u-(-t))) T (-q.2.2.2.2.val)‖^2)≤E*(1+‖u‖)^(2*J)) :
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
  refine Finset.sum_congr rfl fun q hq => ?_
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
