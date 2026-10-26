import Candidate.Cycle63.Physical.InitialMass.GeometryContraction
import Candidate.Uneven.GeometryPayment
import Candidate.Cycle63.Physical.InitialMass.JointWindowEnergy
import Candidate.Uneven.Columns
import Candidate.Cycle63.Physical.InitialMass.GeometrySources

/- Original module: Candidate.Uneven.Energy. -/
section
/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Uneven
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
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow FourierBridge Cycle63Moment RayFourExpansion CenteredMomentPrimitive CenteredMomentScale
local notation "O" => HeckeFamily.O

open Cycle63InitialMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal normalized left energy: the original phase and outside scalar
are inside the square, and only the proven geometric power is divided out. -/
def unevenLeftEnergy (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.leftColumn Finset.univ
      (firstJointLeft (geometryFirstSource s R seed K Z ξ hK key) weight q)
      (V 2) (firstLeftLog (geometryFirstSource s R seed K Z ξ hK key q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
        unevenLeft A (geometryExponents s R seed K Z ξ q.1.val))

def unevenRightEnergy (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ)) (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  ∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
    ‖CenteredMomentCauchy.rightColumn Finset.univ
      (firstJointRight (geometryFirstSource s R seed K Z ξ hK key) q)
      (V 3) (firstRightLog (geometryFirstSource s R seed K Z ξ hK key q.1)) t‖^2/
      Z^(unevenRight A (geometryExponents s R seed K Z ξ q.1.val))

omit [DecidableEq ι] in
/-- Applies the cross-label payment to the actual joint first-sector energy.
All divisor, ray and frequency indices remain in the two normalized sums. -/
theorem actual_first_energy_uneven_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hK : 0< K) (hZ : 1< Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ)) (weight : CommonGeometryFiber s R seed K Z ξ key→ℂ)
    (V : Fin 4→ℝ→ℂ) (t : ℝ) :
    firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK key) weight V t ≤
      32*Z^M*Real.sqrt (unevenLeftEnergy s R seed K Z ξ M A hK key weight V t)*
        Real.sqrt (unevenRightEnergy s R seed K Z ξ A hK key V t) := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let L : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft src weight q)
      (V 2) (firstLeftLog (src q.1)) t‖^2/
      Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
        unevenLeft A (geometryExponents s R seed K Z ξ q.1.val))
  let N : FirstSector src→ℝ := fun q=>
    ‖CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight src q)
      (V 3) (firstRightLog (src q.1)) t‖^2/
      Z^(unevenRight A (geometryExponents s R seed K Z ξ q.1.val))
  have hz : 0< Z := zero_lt_one.trans hZ
  let p (q : FirstSector src) := Z^(2*outsideExponent M A
    (geometryExponents s R seed K Z ξ q.1.val)+
      unevenLeft A (geometryExponents s R seed K Z ξ q.1.val))
  let r (q : FirstSector src) := Z^(unevenRight A (geometryExponents s R seed K Z ξ q.1.val))
  have hpair (q u : FirstSector src) : p q*r u≤(32*Z^M)^2 := by
    have hh := actual_uneven_cross_payment s R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key q.1 u.1
    have hp := pow_le_pow_left₀ (by positivity) hh 2
    rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
      Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz] at hp
    convert hp using 1
    dsimp [p,r]
    congr 2
    ring
  have hh := weighted_joint_energy_finset (firstActiveSectors src V) (firstActiveSectors src V)
    p L r N (32*Z^M) (fun _=> Real.rpow_nonneg hz.le _)
    (fun _=> Real.rpow_nonneg hz.le _) (fun _=> by dsimp [L];positivity)
    (fun _=> by dsimp [N];positivity) (by positivity) hpair
  simpa only [p,r,L,N,mul_div_cancel₀ _ (Real.rpow_pos_of_pos hz _).ne',
    firstActiveEnergyPair,unevenLeftEnergy,unevenRightEnergy,src] using hh


end
end OAI.SevenEighths.Target830.Source.Uneven
end

/- Original module: Candidate.Uneven.Windows. -/
section
/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy FourierBridge
local notation "O" => HeckeFamily.O

open Cycle63InitialMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unevenLeftScalar (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  weight q.1.val*(geometryFirstSource s R seed K Z ξ hK key q.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ q.1.val)+
      unevenLeft A (geometryExponents s R seed K Z ξ q.1.val))):ℂ)

omit [DecidableEq ι] in
/-- Specialization to the actual normalized left Hilbert energy in one
geometry group. The original outside scalar, source volume and every
first-sector coordinate are preserved through the Mellin integral. -/
theorem actual_uneven_left_window_energy (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (hseed : ∀q : CommonGeometryFiber s R seed K Z ξ key,
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).C)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 2)) (hs : ContDiff ℝ ∞ (V 2))
    (t T : ℝ) (hT : 0< T) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
        ‖unevenLeftScalar s R seed K Z ξ M A hK key weight q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            (geometryFirstSource s R seed K Z ξ hK key q.1).C q.2.1.val
            (originalFirstPair s R seed K Z ξ hK
              (geometryOriginalSector s R seed K Z ξ hK key q)).left
            (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val‖^2)≤ E*(1+‖u‖)^(2*J)) :
    unevenLeftEnergy s R seed K Z ξ M A hK key (fun q=> weight q.val) V t/T≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity (V 2) hc hs u‖)^2 := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let lift := geometryOriginalSector s R seed K Z ξ hK key
  have hh := actual_joint_first_window_energy (firstActiveSectors src V)
    (fun _ : FirstSector src=> s) (fun _=> R) (fun _=> seed)
    (fun q=>(src q.1).C) (fun q=> q.2.1.val) (fun q=>(src q.1).hC)
    (fun q=> hseed q.1)
    (fun q=>(originalFirstPair s R seed K Z ξ hK (lift q)).left)
    (fun _=> s.t) (fun _=> T) (fun _=> t) (fun q=>(src q.1).A0)
    (fun q=>(src q.1).A0_pos) (fun q=> q.2.2.2.2.val)
    (fun q=> unevenLeftScalar s R seed K Z ξ M A hK key weight q) (V 2) hc hs J E hE henergy
  apply le_trans (le_of_eq ?_) hh
  rw [unevenLeftEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  have hcol := actual_first_left_common_window s R seed K Z ξ hK weight (lift q) (V 2) t
  change CenteredMomentCauchy.leftColumn Finset.univ
    (firstJointLeft src (fun q=> weight q.val) q) (V 2) (firstLeftLog (src q.1)) t=_ at hcol
  rw [hcol]
  dsimp only [unevenLeftScalar]
  simp only [norm_mul,norm_div,norm_inv,mul_pow,div_pow,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),Real.sq_sqrt hT.le]
  dsimp [src,lift,geometryOriginalSector,geometryFirstSource]
  ring

def unevenRightScalar (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  (Real.sqrt (Z^(unevenRight A (geometryExponents s R seed K Z ξ q.1.val))):ℂ)⁻¹

omit [DecidableEq ι] in
/-- The matching right energy uses the reflected row and conjugate window;
its Mellin height is independent of the left one. -/
theorem actual_uneven_right_window_energy (s : Input ι) (R seed : Ideal O)
    (K Z ξ A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (hseed : ∀q : CommonGeometryFiber s R seed K Z ξ key,
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).D)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 3)) (hs : ContDiff ℝ ∞ (V 3))
    (t T : ℝ) (hT : 0< T) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s R seed K Z ξ hK key) V,
        ‖unevenRightScalar s R seed K Z ξ A hK key q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            (geometryFirstSource s R seed K Z ξ hK key q.1).D q.2.1.val
            (originalFirstPair s R seed K Z ξ hK
              (geometryOriginalSector s R seed K Z ξ hK key q)).right
            (s.t+2*Real.pi*(u-(-t))) T (-q.2.2.2.2.val)‖^2)≤ E*(1+‖u‖)^(2*J)) :
    unevenRightEnergy s R seed K Z ξ A hK key V t/T≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=> star (V 3 x))
        (CenteredMomentConjugateWindow.conjugate_compact (V 3) hc)
        (CenteredMomentConjugateWindow.conjugate_smooth (V 3) hs) u‖)^2 := by
  let src := geometryFirstSource s R seed K Z ξ hK key
  let lift := geometryOriginalSector s R seed K Z ξ hK key
  have hh := actual_joint_first_window_energy (firstActiveSectors src V)
    (fun _ : FirstSector src=> s) (fun _=> R) (fun _=> seed)
    (fun q=>(src q.1).D) (fun q=> q.2.1.val) (fun q=>(src q.1).hD)
    (fun q=> hseed q.1)
    (fun q=>(originalFirstPair s R seed K Z ξ hK (lift q)).right)
    (fun _=> s.t) (fun _=> T) (fun _=>-t) (fun q=>(src q.1).B0)
    (fun q=>(src q.1).B0_pos) (fun q=>-q.2.2.2.2.val)
    (fun q=> unevenRightScalar s R seed K Z ξ A hK key q) (fun x=> star (V 3 x))
    (CenteredMomentConjugateWindow.conjugate_compact (V 3) hc)
    (CenteredMomentConjugateWindow.conjugate_smooth (V 3) hs) J E hE henergy
  apply le_trans (le_of_eq ?_) hh
  rw [unevenRightEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  have hcol := actual_first_right_common_window s R seed K Z ξ hK (lift q) (V 3) t
  change CenteredMomentCauchy.rightColumn Finset.univ
    (firstJointRight src q) (V 3) (firstRightLog (src q.1)) t=_ at hcol
  rw [hcol]
  dsimp only [unevenRightScalar]
  simp only [norm_mul,norm_inv,norm_star,mul_pow,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),Real.sq_sqrt hT.le]
  dsimp [src,lift,geometryOriginalSector,geometryFirstSource]
  ring

end
end OAI.SevenEighths.Target830.Source.Uneven
end

/- Original module: Candidate.Uneven.Budget. -/
section
/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy FourierBridge
local notation "O" => HeckeFamily.O

open Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentLogDyadic CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic


lemma inverse_sqrt_rpow_shift (Z e σ : ℝ) (hZ : 0< Z) :
    (Real.sqrt (Z^e))⁻¹*Z^(-σ/2)=(Real.sqrt (Z^(e+σ)))⁻¹ := by
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le,←Real.rpow_neg hZ.le,
    ←Real.rpow_add hZ]
  congr 1
  ring

lemma complex_inverse_sqrt_rpow_shift (Z e σ : ℝ) (hZ : 0< Z) :
    (Real.sqrt (Z^e):ℂ)⁻¹*((Z^(-σ/2):ℝ):ℂ)=
      (Real.sqrt (Z^(e+σ)):ℂ)⁻¹ := by
  exact_mod_cast inverse_sqrt_rpow_shift Z e σ hZ

variable {ι : Type*} [Fintype ι]

theorem unevenColumnScalar_formula (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    unevenColumnScalar reflected s R seed K Z ξ M A hK key weight j=
      if reflected then
        (Real.sqrt (Z^(unevenRight A (geometryExponents s R seed K Z ξ j.1.val))):ℂ)⁻¹
      else weight j.1.val*(geometryFirstSource s R seed K Z ξ hK key j.1).outside/
        (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ j.1.val)+
          unevenLeft A (geometryExponents s R seed K Z ξ j.1.val))):ℂ) := by
  unfold unevenColumnScalar geometryColumnScalar
  cases reflected
  · simp only [Bool.false_eq_true,ite_false]
    rw [left_eq_old]
    simp only [div_eq_mul_inv,mul_assoc]
    have he := complex_inverse_sqrt_rpow_shift Z
      (2*outsideExponent M A (geometryExponents s R seed K Z ξ j.1.val)+
        leftExponent A (geometryExponents s R seed K Z ξ j.1.val))
      (allocation false (geometryExponents s R seed K Z ξ j.1.val)) hZ
    simp only [div_eq_mul_inv] at he
    rw [he]
    congr 3
    ring
  · simp only [ite_true]
    rw [right_eq_old]
    exact complex_inverse_sqrt_rpow_shift Z _ _ hZ


/-- The literal left child budget supplies the source premise of the
Mellin-window theorem, with original source volume as normalization. -/
theorem actual_uneven_left_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0< a) (hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (hbudget : ∀u : ℝ, unevenLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤ E*(1+‖u‖)^(2*J)) :
    unevenLeftEnergy s R seed K Z ξ M A hK key (fun q=> weight q.val)
      (fun _=> logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        logAnnulus hc hsm u‖)^2 := by
  apply actual_uneven_left_window_energy s R seed K Z ξ M A hK hZ key weight
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).1)
    (fun _=> logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_uneven_source_budget false s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-t)) ha hcard haS hbS hs hz₁ hz₂
  simp only [unevenColumnScalar_formula false s R seed K Z ξ M A hK hZ key,
    Bool.false_eq_true,ite_false] at hh
  exact le_trans hh (hbudget u)

/-- The reflected right budget passes through its independent Mellin
height, retaining the conjugate window from the actual first transform. -/
theorem actual_uneven_right_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (hZ : 0< Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0< a) (hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (hbudget : ∀u : ℝ, unevenLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤ E*(1+‖u‖)^(2*J)) :
    unevenRightEnergy s R seed K Z ξ A hK key (fun _=> logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        (fun x=> star (logAnnulus x))
        (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
        (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖)^2 := by
  apply actual_uneven_right_window_energy s R seed K Z ξ A hK hZ key
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).2)
    (fun _=> logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_uneven_source_budget true s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-(-t))) ha hcard haS hbS hs hz₁ hz₂
  simp only [unevenColumnScalar_formula true s R seed K Z ξ M A hK hZ key,
    ite_true] at hh
  exact le_trans hh (hbudget u)

end
end OAI.SevenEighths.Target830.Source.Uneven
end

/- Original module: Candidate.Uneven.MainAssemblyUnevenContraction. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open Target830.Source.Uneven
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentScale
open CenteredMomentFirstSourceReduction CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

/-- The two actual first-source budgets pass through their own Mellin
windows and the cross-label normalization, with no per-label Cauchy shortcut. -/
theorem actual_first_energy_from_uneven_budgets {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι) (R seed : Ideal O)(K Z ξ B M A : ℝ)(hK : 0< K)(hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ)(a b : ℝ)(ha : 0< a)(hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower)(hbS : s.upper≤ b)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ)(J : ℕ)(E H : ℝ)(hE : 0≤ E)(hH : 0< H)
    (hleft : ∀u : ℝ,unevenLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤(E*H)*(1+‖u‖)^(2*J))
    (hright : ∀u : ℝ,unevenLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤(E/H)*(1+‖u‖)^(2*J)) :
    firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK key)
      (fun q=> weight q.val) (fun _=> logAnnulus) t ≤
      32*Z^M*(volume s*E)*
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖| *
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=> star (logAnnulus x))
          (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
          (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖| := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hL := actual_uneven_left_budget_window s R seed K Z ξ M A hK hz key weight
    N a b ha hcard haS hbS hs hz₁ hz₂ hc hsm t J (E*H) (mul_nonneg hE hH.le) hleft
  have hR := actual_uneven_right_budget_window s R seed K Z ξ M A hK hz key weight
    N a b ha hcard haS hbS hs hz₁ hz₂ hc hsm t J (E/H) (div_nonneg hE hH.le) hright
  let IL := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=> star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  have hv := volume_pos s
  have hve : 0≤ volume s*E := mul_nonneg hv.le hE
  have hLe : unevenLeftEnergy s R seed K Z ξ M A hK key (fun q=> weight q.val)
      (fun _=> logAnnulus) t≤(volume s*(E*H))*IL^2 := by
    have hh := (div_le_iff₀ hv).mp hL
    simpa only [IL,mul_assoc,mul_comm,mul_left_comm] using hh
  have hRe : unevenRightEnergy s R seed K Z ξ A hK key (fun _=> logAnnulus) t≤
      (volume s*(E/H))*IR^2 := by
    have hh := (div_le_iff₀ hv).mp hR
    simpa only [IR,mul_assoc,mul_comm,mul_left_comm] using hh
  have hLs := Real.sqrt_le_sqrt hLe
  have hRs := Real.sqrt_le_sqrt hRe
  rw [Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hLs
  rw [Real.sqrt_mul (mul_nonneg hv.le (div_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hRs
  have hprod := mul_le_mul hLs hRs (Real.sqrt_nonneg _) (by positivity)
  have hh := actual_first_energy_uneven_payment s R seed K Z ξ B M A hK hZ hs hz₁ hz₂
    hsource key (fun q=> weight q.val) (fun _=> logAnnulus) t
  apply hh.trans
  calc
    _≤(32*Z^M)*((Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by positivity : 0≤32*Z^M)
    _=_ := by
      have heq : (Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)=
          (volume s*E)*|IL| *|IR| := by
        have hp : (volume s*(E*H))*(volume s*(E/H))=(volume s*E)^2 := by
          field_simp
        have hr : Real.sqrt (volume s*(E*H))*Real.sqrt (volume s*(E/H))=volume s*E := by
          rw [←Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),hp,Real.sqrt_sq hve]
        calc
          _=(Real.sqrt (volume s*(E*H))*Real.sqrt (volume s*(E/H)))*|IL| *|IR| := by ring
          _=_ := by rw [hr]
      rw [heq]
      dsimp only [IL,IR]
      ring


/-- The remaining analytic input is a bound on the literal normalized
live-source budgets. Both Mellin integrals and original physical contraction
are discharged here, uniformly before moving sources and geometry bins. -/
theorem actual_physical_mass_from_uneven_budgets {ι : Type*}[Fintype ι][DecidableEq ι]
    (W : 𝓢(ℝ,ℂ))(decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀(s : Input ι)(R seed : Ideal O)(K Z ξ B M A : ℝ)
      (hK : 0< K)(hZ : 1< Z)(N : ℕ)(a b : ℝ),0< a → Fintype.card ι≤ N →
      a≤ s.lower → s.upper≤ b → Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B →
      ∀E H : ℤ×(Fin 5→ℤ)→ℝ,(∀key∈commonGeometryBins s R seed K Z ξ,0≤ E key) →
      (∀key∈commonGeometryBins s R seed K Z ξ,0< H key) →
      (∀key∈commonGeometryBins s R seed K Z ξ,∀(reflected : Bool)(t u : ℝ),
        unevenLiveBudget reflected s R seed K Z ξ M A hK key
          (fun q=> normPhase (coordinateBlock s R seed W K Z ξ q)) N b
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
          ((if reflected then E key/H key else E key*H key)*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) →
      physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*Z^M*volume s*∑key∈commonGeometryBins s R seed K Z ξ,
          E key/(1+dyadicScale key.1)^decay := by
  obtain ⟨C,hC,hphysical⟩ := actual_physical_mass_geometry_contraction (ι:=ι) W decay degree
  let IL := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=> star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  refine ⟨C*32*|IL| *|IR|,by positivity,?_⟩
  intro s R seed K Z ξ B M A hK hZ N a b ha hn haS hbS hs hz₁ hz₂ hsource E H hE hH hbudget
  let factor := 32*Z^M*volume s*|IL| *|IR|
  have hf : 0≤ factor := by
    have hv := (volume_pos s).le
    have hz := (zero_lt_one.trans hZ).le
    dsimp [factor]
    positivity
  have hh := hphysical s R seed K Z ξ hK (fun key=> factor*E key)
    (fun key hk=> mul_nonneg hf (hE key hk)) (by
      intro key hk t
      have he := actual_first_energy_from_uneven_budgets s R seed K Z ξ B M A hK hZ
        key (fun q=> normPhase (coordinateBlock s R seed W K Z ξ q)) N a b ha hn haS hbS
        hs hz₁ hz₂ hsource hc hsm t windowDegree (E key*(1+‖t‖)^degree) (H key)
        (mul_nonneg (hE key hk) (by positivity)) (hH key hk)
        (fun u=> by simpa only [Bool.false_eq_true,ite_false,mul_assoc,mul_comm,mul_left_comm] using hbudget key hk false t u)
        (fun u=> by simpa only [ite_true,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hbudget key hk true t u)
      apply he.trans_eq
      dsimp only [factor,IL,IR]
      ring)
  apply hh.trans_eq
  simp only [mul_div_assoc,←Finset.mul_sum]
  dsimp only [factor]
  ring



end
end OAI.SevenEighths.MainAssembly
end
