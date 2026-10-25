/- Copyright (c) 2026 Sil. Apache-2.0.
Joint numerical payment of the four ACTUAL first-side costs. All sixteen
cross terms, both distinct nominal child scales, original prefixes and
the artificial divisor are retained. No energy estimate is a premise.

-/
import Candidate.SilPrior.FourthPower.MixedFirstFullBudget
import Candidate.SilPrior.FourthPower.MixedFirstGeometricCaps
import Candidate.SilPrior.FourthPower.MixedFirstNonexceptionalNormalization
import Candidate.SilPrior.FourthPower.MixedSelectedVolume
import Candidate.SilPrior.FourthPower.MixedFirstCutoffs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstPaidCosts
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentFirstMixedAllowance
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSecondHeightFamily CenteredMomentSourceProfileMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondWindowSource
open CenteredMomentSecondWindowBudget CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos ideal_norm_one_le)
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalBudget MixedPrincipalCentered MixedOriginalTail
open MixedHeightEnvelope
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstExceptionalNormalization MixedFirstExceptionalWindow MixedFirstExceptionalApplication
open MixedFirstFullBudget MixedFirstGeometricCaps MixedFirstNonexceptionalNormalization
open MixedFirstNonexceptionalAllocation
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The equality case belongs to the uncentered branch, and is paid by
the final arbitrarily small loss. In the centered case the same l also
satisfies the upper reference gate, not only the exceptional inequality. -/
def ReferenceChoice (R P S d l : ℝ) : Prop :=
  (l=0 ∧ P+S≤5*R/6-7*d/3) ∨
  (5*R/6-7*d/3<P+S ∧ MixedLedger.lower R P S d<l ∧
    l<MixedLedger.upper R P S d)

theorem exists_reference_choice (R P S d : ℝ) (hgate : P+2*S+4*d<R) :
    ∃l : ℝ,ReferenceChoice R P S d l := by
  by_cases h : P+S≤5*R/6-7*d/3
  · exact ⟨0,Or.inl ⟨rfl,h⟩⟩
  · obtain ⟨l,hl,hu⟩ := MixedLedger.reference_interval_nonempty hgate
    exact ⟨l,Or.inr ⟨lt_of_not_ge h,hl,hu⟩⟩

theorem reference_choice_bounds {R P S d l : ℝ} (h : ReferenceChoice R P S d l) :
    0≤l ∧ P+S-5*R/6+7*d/3-2*l/3≤0 := by
  rcases h with ⟨rfl,h⟩|⟨hc,hl,hu⟩
  · constructor <;> linarith
  · dsimp only [MixedLedger.lower] at hl
    constructor <;> linarith

/-- The selected-window gates for the literal padded slot product.
The fixed padding bound is supplied uniformly by SelectedVolume;
there is no assumed single-dyadic upper bound on selected products. -/
theorem actual_padding_gates {α : Type*} [Fintype α]
    (q : MixedSupplierFourthRow.Data α) (hP : ∀i,0<q.P i)
    (Z d omega : ℝ) (hZ : 1<Z)
    (hvol : MixedSelectedVolume.volume q=Z^d)
    (hpad : MixedSelectedVolume.padding q≤Z^omega) :
    Z^d≤MixedSelectedVolume.scale q ∧
      Real.logb Z (MixedSelectedVolume.scale q)≤d+omega := by
  have hz := zero_lt_one.trans hZ
  have hp1 : 1≤MixedSelectedVolume.padding q := by
    unfold MixedSelectedVolume.padding
    exact one_le_pow₀ (by norm_num)
  have hscale := MixedSelectedVolume.scale_pos q hP
  have hup : MixedSelectedVolume.scale q≤Z^(d+omega) := by
    unfold MixedSelectedVolume.scale
    rw [hvol]
    calc
      _≤Z^omega*Z^d := mul_le_mul_of_nonneg_right hpad (Real.rpow_nonneg hz.le _)
      _=_ := by rw [←Real.rpow_add hz];congr 1;ring
  constructor
  · unfold MixedSelectedVolume.scale
    rw [hvol]
    nlinarith [Real.rpow_nonneg hz.le d]
  · have hh := Real.logb_le_logb_of_le hZ hscale hup
    rwa [Real.logb_rpow hz hZ.ne'] at hh

/-- Scalars of the actual source application. W is already the padded
selected scale. Its only padding cost is the explicit omega in log W.
sigma bounds the one retained-frequency loss plus child padding. -/
structure Parameters where
  Z : ℝ
  Kfirst : ℝ
  Tfirst : ℝ
  Cfirst : ℝ
  ξfirst : ℝ
  κpad : ℝ
  W : ℝ
  ε : ℝ
  δ : ℝ
  Bnorm : ℝ
  BG : ℝ
  BX : ℝ
  R : ℝ
  P : ℝ
  S : ℝ
  d : ℝ
  l : ℝ
  c0 : ℝ
  omega : ℝ
  sigma : ℝ
  loss : ℝ
  saving : ℝ

/-- Only numerical and geometric gates; no analytical estimate fields. -/
structure Gates (p : Parameters) : Prop where
  hZ : 1<p.Z
  hK : 0<p.Kfirst
  hW : 0<p.W
  hc0 : 0<p.c0
  hCfirst : 1≤p.Cfirst
  hξ : 0≤p.ξfirst
  hε : 0≤p.ε
  hδ : 0≤p.δ
  hS : 0≤p.S
  hd : 0≤p.d
  mixed : p.P+2*p.S+4*p.d<p.R
  native : (3/4:ℝ)*p.S<p.d
  reference : ReferenceChoice p.R p.P p.S p.d p.l
  Wlower : p.Z^p.d≤p.W
  Wupper : Real.logb p.Z p.W≤p.d+p.omega
  frequency : frequencyLoss p.Z p.Cfirst p.ξfirst+p.κpad≤p.sigma
  zero_loss : p.BG*p.δ+p.BX*p.ε+3*p.omega+p.sigma≤p.loss
  native_loss : 2*p.ε+(p.BG+1)*p.δ≤p.loss
  exceptional_loss : 3*p.ε+(2*p.Bnorm+p.BG)*p.δ+7*p.omega/3+5*p.sigma/6≤p.loss
  tail_loss : p.BG*(1+p.δ)-p.saving≤p.loss

structure SourceGeometry (p : Parameters) (s : Source ι a b) (η : Character)
    (w : ι→ℝ) : Prop where
  volume : Real.logb p.Z (sourceVolume s)≤p.P+p.S
  width : p.R ≤ inputWidth η p.Kfirst p.Z
  length : p.c0*p.Z^p.l≤s.L
  support : sharpSupport s≤p.Z^p.BX
  slots : (∑i,w i)≤p.S

/-- A literal fixed first side. The two sides may have different G,
opposite common, character, height and therefore different child scale. -/
structure Side (p : Parameters) (s : Source ι a b) (η : Character) where
  G : Id
  Gopp : Id
  τ : Character
  height : ℝ
  E : Finset (CommonIndex G Gopp)
  n : ℤ
  hG : Supported G
  hGopp : Supported Gopp
  common : CompletedGauss.primeSupport G=CompletedGauss.primeSupport Gopp
  cap : (G.absNorm:ℝ)≤p.Z^p.BG
  modulus : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex G Gopp=>P.val) E*activeConductor G Gopp}
  frequency : p.Tfirst≤p.Cfirst*firstNominalScale G Gopp
    (Ideal.span {primeSubsetGenerator (fun P : CommonIndex G Gopp=>P.val) E})
    p.Kfirst (sourceVolume s)
  retained : Retained (frequencyRadius p.Tfirst p.Z p.ξfirst) n

def Side.child {p : Parameters} {s : Source ι a b} {η : Character} (x : Side p s η) : ℝ :=
  nominalChildScale x.G x.Gopp x.E p.Kfirst (sourceVolume s) p.Z p.κpad x.n

def costs (U : Controls) (c : Constants) (s : Source ι a b) (η : Character)
    (Dart Q : Id) (w : ι→ℝ) (t V : ℝ) (p : Parameters) (x : Side p s η) : Fin 4→ℝ :=
  normalizedCosts U c s η x.τ x.G x.Gopp Dart Q w p.Bnorm p.Z p.ε p.δ (3/4)
    t V x.height (sharpSupport s) p.Kfirst x.child p.Cfirst p.ξfirst p.κpad p.W p.saving

/-- These are explicit fixed/profile coefficients, with no powers of Z
from analytical losses. Prefix costs remain 1/p, 1/p^2 and H^(2/3)/p^(4/3).
The fixed subunit reference scale costs c0^(-2/3) in the exceptional
entry and c0^(-4) in the tail. The artificial divisor stays separate. -/
def coefficients (U : Controls) (c : Constants) (s : Source ι a b)
    (Q : Id) (c0 t V tp : ℝ) : Fin 4→ℝ :=
  ![16*‖paperRadialFourier ballProfile 0‖*c.zero*(∏i,s.M i)^2*(profileCap s)^2*
      supportConstant b (Fintype.card ι)/pairNorm s.d,
    c.nonexceptionalCount*profileFactor s U.nonexceptionalDegree c.physical c.geometry
      (canonicalProfile U c s t V) tp/(pairNorm s.d)^2,
    (c.kernel*c.exceptional*heightBase tp^(2*U.exceptionalDegree)*(windowMoment U.exceptionalDegree)^2)*
      c.exceptionalSum*c.exceptionalCount*
      originalFactor s U.exceptionalDegree U.exceptionalControl Q 1 0*
      (prefixNormMax s.d)^(2/3:ℝ)*c0^(-2/3:ℝ),
    c.tail*(∏i,s.M i)^2*(profileCap s)^2*
      U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile/c0^4]

private theorem canonical_nonneg (U : Controls) (c : Constants) (s : Source ι a b)
    (t V : ℝ) (hV : 0≤V) : 0≤canonicalProfile U c s t V := by
  have hd := diagonalControl_nonneg ballProfile
  have ht := sourceHeight_one_le t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi)) hV
  have hc := c.source_pos
  unfold canonicalProfile
  positivity

theorem coefficients_nonneg (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (Q : Id) (c0 t V tp : ℝ) (hc0 : 0<c0) (hV : 0≤V) :
    ∀i,0≤coefficients U c s Q c0 t V tp i := by
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hA := canonical_nonneg U c s t V hV
  have hn := profileFactor_nonneg s U.nonexceptionalDegree c.physical c.geometry
    (canonicalProfile U c s t V) tp c.physical_pos.le c.geometry_pos.le hA
  have he := originalFactor_nonneg s ha U.exceptionalDegree U.exceptionalControl Q 1 0
  have hz := c.zero_pos
  have hcount := c.nonexceptionalCount_pos
  have hk := c.kernel_nonneg
  have hex := c.exceptional_pos
  have hs := c.exceptionalSum_pos
  have hce := c.exceptionalCount_pos
  have ht := c.tail_pos
  have hH := prefixNormMax_pos s.d s.hd
  have hheight : 0 ≤ heightBase tp := by unfold heightBase; positivity
  intro i
  fin_cases i
  · change 0 ≤ 16*‖paperRadialFourier ballProfile 0‖*c.zero*(∏i,s.M i)^2*
      (profileCap s)^2*supportConstant b (Fintype.card ι)/pairNorm s.d
    unfold supportConstant
    positivity
  · change 0 ≤ c.nonexceptionalCount*profileFactor s U.nonexceptionalDegree
      c.physical c.geometry (canonicalProfile U c s t V) tp/(pairNorm s.d)^2
    exact div_nonneg (mul_nonneg hcount.le hn) (sq_nonneg _)
  · change 0 ≤ (c.kernel*c.exceptional*heightBase tp^(2*U.exceptionalDegree)*
      (windowMoment U.exceptionalDegree)^2)*c.exceptionalSum*c.exceptionalCount*
      originalFactor s U.exceptionalDegree U.exceptionalControl Q 1 0*
      (prefixNormMax s.d)^(2/3:ℝ)*c0^(-2/3:ℝ)
    positivity
  · change 0 ≤ c.tail*(∏i,s.M i)^2*(profileCap s)^2*
      U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile/c0^4
    positivity

private theorem common_power {p : Parameters} (h : Gates p)
    {s : Source ι a b} {η : Character} (x : Side p s η) :
    (x.G.absNorm:ℝ)^p.δ≤p.Z^(p.BG*p.δ) := by
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) x.cap h.hδ
  rwa [←Real.rpow_mul (zero_lt_one.trans h.hZ).le] at hp

private theorem volume_lower {p : Parameters} (h : Gates p)
    {s : Source ι a b} {η : Character} {w : ι→ℝ} (g : SourceGeometry p s η w) :
    p.c0^2≤sourceVolume s := by
  have hl := (reference_choice_bounds h.reference).1
  have hsL : p.c0≤s.L := by
    calc
      _=p.c0*1 := by ring
      _≤p.c0*p.Z^p.l := mul_le_mul_of_nonneg_left (Real.one_le_rpow h.hZ.le hl) h.hc0.le
      _≤_ := g.length
  have hprod : p.c0^2≤s.X₁*s.X₂ := by
    simpa only [pow_two] using mul_le_mul (hsL.trans s.hX₁) (hsL.trans s.hX₂)
      h.hc0.le (s.hL.trans_le s.hX₁).le
  unfold sourceVolume
  exact hprod.trans (le_mul_of_one_le_right
    (mul_nonneg (s.hL.trans_le s.hX₁).le (s.hL.trans_le s.hX₂).le)
    (Finset.one_le_prod₀ (fun i _=>s.hP i)))

private theorem original_factor_loss (s : Source ι a b) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε : ℝ) (hZ : 0<Z) :
    originalFactor s J control Q Z ε=originalFactor s J control Q 1 0*Z^(2*ε) := by
  have hs : sourceProfile s J control Z ε=sourceProfile s J control 1 0*Z^ε := by
    simp only [sourceProfile,Real.rpow_zero,one_mul,mul_one]
    ring
  have hp : (Z^ε)^2=Z^(2*ε) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  unfold originalFactor
  rw [hs,mul_pow,hp]
  ring

private theorem zero_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (hb : 0<b) (η : Character) (Dart Q : Id) (hDart : Dart≠0) (w : ι→ℝ)
    (t V : ℝ) (p : Parameters) (h : Gates p) (g : SourceGeometry p s η w) (x : Side p s η) :
    costs U c s η Dart Q w t V p x 0≤
      coefficients U c s Q p.c0 t V x.height 0/(Dart.absNorm:ℝ)*p.Z^p.loss := by
  have hz := zero_lt_one.trans h.hZ
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hx := sharp_support_pos s hb
  have hD : 0<(Dart.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDart)
  have hdiag := actual_diagonal_ratio s hb η x.τ x.G x.Gopp Dart hDart
    x.hG x.hGopp x.common x.E p.Kfirst p.Z p.Tfirst p.Cfirst p.ξfirst p.κpad p.W p.ε
    h.hK h.hZ h.hCfirst h.hξ h.hW x.modulus x.frequency x.n x.retained
  have hc := c.zero_pos
  let A := 16*‖paperRadialFourier ballProfile 0‖*c.zero*(∏i,s.M i)^2*(profileCap s)^2
  have hA : 0≤A := by dsimp only [A];positivity
  have hg := common_power h x
  have hxp := Real.rpow_le_rpow hx.le g.support h.hε
  rw [←Real.rpow_mul hz.le] at hxp
  have hg0 := Real.rpow_nonneg (Nat.cast_nonneg x.G.absNorm) p.δ
  have hgeom : Real.logb p.Z (sourceVolume s)-inputWidth η p.Kfirst p.Z+
      3*Real.logb p.Z p.W+frequencyLoss p.Z p.Cfirst p.ξfirst+p.κpad+
      p.BG*p.δ+p.BX*p.ε≤p.loss := by
    have hd := MixedLedger.second_diagonal_gate h.hS h.hd h.mixed
    linarith [g.volume,g.width,h.Wupper,h.frequency,h.zero_loss]
  calc
    _=(A*(x.G.absNorm:ℝ)^p.δ)*
      ((x.child*p.W^3*(sharpSupport s)^(1+p.ε)/((x.G.absNorm:ℝ)*(Dart.absNorm:ℝ)))/
        reference x.τ x.G x.Gopp (sourceVolume s) p.Z) := by
      simp only [costs,normalizedCosts,rawCosts,zeroCost,A,Side.child,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      ring
    _≤(A*(x.G.absNorm:ℝ)^p.δ)*
      ((supportConstant b (Fintype.card ι)/(pairNorm s.d*(Dart.absNorm:ℝ)))*(sharpSupport s)^p.ε*
        p.Z^(Real.logb p.Z (sourceVolume s)-inputWidth η p.Kfirst p.Z+
          3*Real.logb p.Z p.W+frequencyLoss p.Z p.Cfirst p.ξfirst+p.κpad)) :=
      mul_le_mul_of_nonneg_left hdiag (mul_nonneg hA hg0)
    _≤(A*p.Z^(p.BG*p.δ))*
      ((supportConstant b (Fintype.card ι)/(pairNorm s.d*(Dart.absNorm:ℝ)))*p.Z^(p.BX*p.ε)*
        p.Z^(Real.logb p.Z (sourceVolume s)-inputWidth η p.Kfirst p.Z+
          3*Real.logb p.Z p.W+frequencyLoss p.Z p.Cfirst p.ξfirst+p.κpad)) := by
      have hs0 : 0≤supportConstant b (Fintype.card ι) := by unfold supportConstant;positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hg hA)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxp (div_nonneg hs0 (mul_nonneg hp.le hD.le)))
          (Real.rpow_nonneg hz.le _))
        (by positivity) (mul_nonneg hA (Real.rpow_nonneg hz.le _))
    _=(coefficients U c s Q p.c0 t V x.height 0/(Dart.absNorm:ℝ))*
      p.Z^(Real.logb p.Z (sourceVolume s)-inputWidth η p.Kfirst p.Z+
        3*Real.logb p.Z p.W+frequencyLoss p.Z p.Cfirst p.ξfirst+p.κpad+
        p.BG*p.δ+p.BX*p.ε) := by
      simp only [coefficients,A,Real.rpow_add hz,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le h.hZ.le hgeom)
      (by simp only [coefficients,Matrix.cons_val_zero];unfold supportConstant;positivity)

private theorem native_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (η : Character) (Dart Q : Id) (hDart : Dart≠0) (w : ι→ℝ)
    (t V : ℝ) (hV : 0≤V) (p : Parameters) (h : Gates p)
    (g : SourceGeometry p s η w) (x : Side p s η) :
    costs U c s η Dart Q w t V p x 1≤
      coefficients U c s Q p.c0 t V x.height 1/(Dart.absNorm:ℝ)*p.Z^p.loss := by
  have hA := canonical_nonneg U c s t V hV
  have he := native_cost_power s x.τ x.G x.Gopp Dart x.hG.1 hDart U.nonexceptionalDegree w
    c.nonexceptionalCount c.physical c.geometry p.Z (canonicalProfile U c s t V)
    x.height p.W p.ε p.δ p.BG p.d h.hZ h.hW c.nonexceptionalCount_pos.le
    c.physical_pos.le c.geometry_pos.le hA h.hδ x.cap h.Wlower
  have hpow : (3/4:ℝ)*(∑i,w i)-p.d+2*p.ε+(p.BG+1)*p.δ≤p.loss := by
    linarith [g.slots,h.native,h.native_loss]
  have hf := profileFactor_nonneg s U.nonexceptionalDegree c.physical c.geometry
    (canonicalProfile U c s t V) x.height c.physical_pos.le c.geometry_pos.le hA
  simp only [costs,normalizedCosts,rawCosts,nonexceptionalCost,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  apply he.trans
  convert mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h.hZ.le hpow)
    (div_nonneg (mul_nonneg c.nonexceptionalCount_pos.le hf)
      (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg Dart.absNorm))) using 1 <;>
    simp only [costs,normalizedCosts,rawCosts,nonexceptionalCost,coefficients,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] <;> ring

private theorem exceptional_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (η : Character) (Dart Q : Id) (hDart : Dart≠0) (w : ι→ℝ)
    (t V : ℝ) (p : Parameters) (h : Gates p) (g : SourceGeometry p s η w) (x : Side p s η) :
    costs U c s η Dart Q w t V p x 2≤
      coefficients U c s Q p.c0 t V x.height 2/(Dart.absNorm:ℝ)*p.Z^p.loss := by
  have hz := zero_lt_one.trans h.hZ
  have href := MixedFirstFullBudget.reference_pos s x.τ x.G x.Gopp x.hG.1 p.Z hz
  have hH := prefixNormMax_pos s.d s.hd
  have hLlog := Real.logb_le_logb_of_le h.hZ
    (mul_pos h.hc0 (Real.rpow_pos_of_pos hz p.l)) g.length
  rw [Real.logb_mul h.hc0.ne' (Real.rpow_pos_of_pos hz p.l).ne',
    Real.logb_rpow hz h.hZ.ne'] at hLlog
  have hbase := (reference_choice_bounds h.reference).2
  have hexp : 3*p.ε+(2*p.Bnorm+p.BG)*p.δ+
      referenceExponent s η p.Kfirst p.Z p.Cfirst p.ξfirst p.κpad p.W≤
      p.loss+Real.logb p.Z (prefixNormMax s.d)*(2/3:ℝ)+Real.logb p.Z p.c0*(-2/3:ℝ) := by
    dsimp only [referenceExponent] at ⊢
    have hw := g.width
    dsimp only [inputWidth] at hw
    linarith [g.volume,h.Wupper,h.frequency,h.exceptional_loss]
  have hHpow : p.Z^(Real.logb p.Z (prefixNormMax s.d)*(2/3:ℝ))=
      (prefixNormMax s.d)^(2/3:ℝ) := by
    rw [Real.rpow_mul hz.le,Real.rpow_logb hz h.hZ.ne' hH]
  have hc0pow : p.Z^(Real.logb p.Z p.c0*(-2/3:ℝ))=p.c0^(-2/3:ℝ) := by
    rw [Real.rpow_mul hz.le,Real.rpow_logb hz h.hZ.ne' h.hc0]
  let A := (c.kernel*c.exceptional*heightBase x.height^(2*U.exceptionalDegree)*
      (windowMoment U.exceptionalDegree)^2)*c.exceptionalSum*c.exceptionalCount*
      originalFactor s U.exceptionalDegree U.exceptionalControl Q 1 0/(Dart.absNorm:ℝ)
  have ho := originalFactor_nonneg s ha U.exceptionalDegree U.exceptionalControl Q 1 0
  have hk := c.kernel_nonneg
  have he := c.exceptional_pos
  have hs := c.exceptionalSum_pos
  have hc := c.exceptionalCount_pos
  have hheight : 0 ≤ heightBase x.height := by unfold heightBase; positivity
  have hA : 0≤A := by dsimp only [A];positivity
  have hg := common_power h x
  have heps : p.Z^(3*p.ε)=p.Z^p.ε*p.Z^(2*p.ε) := by
    rw [←Real.rpow_add hz]
    congr 1
    ring
  calc
    _=A*(x.G.absNorm:ℝ)^p.δ*
      p.Z^(3*p.ε+2*p.Bnorm*p.δ+
        referenceExponent s η p.Kfirst p.Z p.Cfirst p.ξfirst p.κpad p.W) := by
      simp only [costs,normalizedCosts,rawCosts,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      rw [mul_div_cancel_left₀ _ href.ne']
      unfold numericalCost
      rw [original_factor_loss s _ _ Q p.Z p.ε hz]
      simp only [A,Real.rpow_add hz,heps]
      ring
    _≤A*p.Z^(p.BG*p.δ)*
      p.Z^(3*p.ε+2*p.Bnorm*p.δ+
        referenceExponent s η p.Kfirst p.Z p.Cfirst p.ξfirst p.κpad p.W) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hA)
        (Real.rpow_nonneg hz.le _)
    _=A*p.Z^(3*p.ε+(2*p.Bnorm+p.BG)*p.δ+
        referenceExponent s η p.Kfirst p.Z p.Cfirst p.ξfirst p.κpad p.W) := by
      rw [mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _≤A*p.Z^(p.loss+Real.logb p.Z (prefixNormMax s.d)*(2/3:ℝ)+Real.logb p.Z p.c0*(-2/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h.hZ.le hexp) hA
    _=_ := by
      rw [Real.rpow_add hz,Real.rpow_add hz,hHpow,hc0pow]
      simp only [coefficients,A,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      ring

private theorem tail_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (η : Character) (Dart Q : Id) (hDart : Dart≠0) (w : ι→ℝ)
    (t V : ℝ) (p : Parameters) (h : Gates p) (g : SourceGeometry p s η w) (x : Side p s η) :
    costs U c s η Dart Q w t V p x 3≤
      coefficients U c s Q p.c0 t V x.height 3/(Dart.absNorm:ℝ)*p.Z^p.loss := by
  have hz := zero_lt_one.trans h.hZ
  have hg : 0<(x.G.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le x.hG.1)
  have hτ := ideal_norm_one_le x.τ.modulus_ne_bot
  have ht : 0<(x.τ.modulus.absNorm:ℝ) := zero_lt_one.trans_le hτ
  have hD : 0<(Dart.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDart)
  have hv0 := sourceVolume_pos s
  have hpow := Real.rpow_pos_of_pos hz (allowance x.G x.Gopp p.Z)
  have hv := volume_lower h g
  have hallow := Real.one_le_rpow h.hZ.le (allowance_nonneg x.G x.Gopp p.Z)
  have hv2 : p.c0^4≤(sourceVolume s)^2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg p.c0) hv 2
    simpa only [←pow_mul] using hh
  have hden : p.c0^4≤(x.τ.modulus.absNorm:ℝ)*(sourceVolume s)^2*p.Z^(allowance x.G x.Gopp p.Z) := by
    calc
      _≤(sourceVolume s)^2 := hv2
      _≤(x.τ.modulus.absNorm:ℝ)*(sourceVolume s)^2 := le_mul_of_one_le_left (sq_nonneg _) hτ
      _≤_ := le_mul_of_one_le_right (mul_nonneg ht.le (sq_nonneg _)) hallow
  have hcap := Real.rpow_le_rpow (Nat.cast_nonneg _) x.cap (by linarith [h.hδ] : 0≤1+p.δ)
  rw [←Real.rpow_mul hz.le] at hcap
  let A := (c.tail*(∏i,s.M i)^2*(profileCap s)^2*
    U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)/(Dart.absNorm:ℝ)
  have hc := c.tail_pos
  have hA : 0≤A := by dsimp only [A,coefficients];positivity
  calc
    _=A*(x.G.absNorm:ℝ)^(1+p.δ)*p.Z^(-p.saving)/
        ((x.τ.modulus.absNorm:ℝ)*(sourceVolume s)^2*p.Z^(allowance x.G x.Gopp p.Z)) := by
      simp only [costs,normalizedCosts,rawCosts,tailCost,A,coefficients,reference,
        Real.rpow_add hg,Real.rpow_one,div_pow,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      field_simp [hg.ne',ht.ne',hD.ne',hv0.ne',hpow.ne']
      <;> ring
    _≤(A*(x.G.absNorm:ℝ)^(1+p.δ)*p.Z^(-p.saving))/p.c0^4 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos h.hc0 4) hden
    _=(A/p.c0^4)*(x.G.absNorm:ℝ)^(1+p.δ)*p.Z^(-p.saving) := by ring
    _≤(A/p.c0^4)*p.Z^(p.BG*(1+p.δ))*p.Z^(-p.saving) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcap (div_nonneg hA (pow_nonneg h.hc0.le 4)))
        (Real.rpow_nonneg hz.le _)
    _=(A/p.c0^4)*p.Z^(p.BG*(1+p.δ)-p.saving) := by rw [mul_assoc,←Real.rpow_add hz];rfl
    _≤(A/p.c0^4)*p.Z^p.loss := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le h.hZ.le h.tail_loss)
      (div_nonneg hA (pow_nonneg h.hc0.le 4))
    _=_ := by
      simp only [A,coefficients,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      ring

/-- All four actual normalized costs, with one common loss. The proof
uses their concrete definitions and the checked actual diagonal/native/
exceptional geometry; it does not accept four energy-bound hypotheses. -/
theorem actual_costs_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (hb : 0<b) (η : Character) (Dart Q : Id) (hDart : Dart≠0)
    (w : ι→ℝ) (t V : ℝ) (hV : 0≤V) (p : Parameters) (h : Gates p)
    (g : SourceGeometry p s η w) (x : Side p s η) :
    ∀i,costs U c s η Dart Q w t V p x i≤
      coefficients U c s Q p.c0 t V x.height i/(Dart.absNorm:ℝ)*p.Z^p.loss := by
  intro i
  fin_cases i
  · exact zero_paid U c s hb η Dart Q hDart w t V p h g x
  · exact native_paid U c s η Dart Q hDart w t V hV p h g x
  · exact exceptional_paid U c s ha η Dart Q hDart w t V p h g x
  · exact tail_paid U c s η Dart Q hDart w t V p h g x

private theorem costs_nonneg (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (η : Character) (Dart Q : Id) (w : ι→ℝ) (t V : ℝ) (hV : 0≤V)
    (p : Parameters) (h : Gates p) (x : Side p s η) :
    ∀i,0≤costs U c s η Dart Q w t V p x i := by
  have hz := zero_lt_one.trans h.hZ
  have href := MixedFirstFullBudget.reference_pos s x.τ x.G x.Gopp x.hG.1 p.Z hz
  have hchild : 0<x.child := Real.rpow_pos_of_pos hz _
  have hA := canonical_nonneg U c s t V hV
  have hfixed := fixedBudget_nonneg U.nonexceptionalDegree c.physical c.geometry p.Z
    ((3/4:ℝ)*(∑i,w i)+2*p.ε+p.δ) (canonicalProfile U c s t V)
    b x.height p.W c.physical_pos.le c.geometry_pos.le hz.le hA h.hW.le
  have hfac := originalFactor_nonneg s ha U.exceptionalDegree U.exceptionalControl Q p.Z p.ε
  have hc0 := c.zero_pos
  have hcn := c.nonexceptionalCount_pos
  have hce := c.exceptional_pos
  have hcs := c.exceptionalSum_pos
  have hcc := c.exceptionalCount_pos
  have hck := c.kernel_nonneg
  have hct := c.tail_pos
  have hW := h.hW
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hv := sourceVolume_pos s
  have hx : 0 ≤ sharpSupport s := by
    rw [sharp_support_eq]
    unfold supportConstant
    positivity
  have hheight : 0 ≤ heightBase x.height := by unfold heightBase; positivity
  intro i
  fin_cases i
  · change 0 ≤ zeroCost c s x.G Dart p.Z p.ε p.δ (sharpSupport s) x.child p.W /
      reference x.τ x.G x.Gopp (sourceVolume s) p.Z
    unfold zeroCost
    positivity
  · change 0 ≤ nonexceptionalCost U c s x.G Dart x.τ w p.Z p.ε p.δ (3/4)
      t V x.height p.W / reference x.τ x.G x.Gopp (sourceVolume s) p.Z
    unfold nonexceptionalCost fullCost
    positivity
  · change 0 ≤ (reference x.τ x.G x.Gopp (sourceVolume s) p.Z *
      numericalCost s η x.G Dart Q U.exceptionalDegree U.exceptionalControl
        p.Bnorm p.ε p.δ p.ε p.δ c.kernel c.exceptional c.exceptionalSum c.exceptionalCount
        p.Z p.Kfirst p.Cfirst p.ξfirst p.κpad p.W x.height) /
      reference x.τ x.G x.Gopp (sourceVolume s) p.Z
    unfold numericalCost
    positivity
  · change 0 ≤ tailCost U c s x.G Dart p.Z p.δ p.saving /
      reference x.τ x.G x.Gopp (sourceVolume s) p.Z
    unfold tailCost
    positivity

/-- Simultaneous payment of ALL sixteen cross pairs. In particular
neither zero/exceptional nor native/tail pairs are omitted. Both child
scales remain the literal independent Side.child values. The actual
artificial-divisor saving is exactly 1/N(Dart), even on cross pairs. -/
theorem actual_sixteen_pairs_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (hb : 0<b) (η : Character) (Dart Q : Id) (hDart : Dart≠0)
    (w : ι→ℝ) (t V : ℝ) (hV : 0≤V) (p : Parameters) (h : Gates p)
    (g : SourceGeometry p s η w) (left right : Side p s η) :
    (∑i : Fin 4,∑j : Fin 4,
      Real.sqrt (costs U c s η Dart Q w t V p left i*
        costs U c s η Dart Q w t V p right j))≤
    p.Z^p.loss/(Dart.absNorm:ℝ)*
      ∑i : Fin 4,∑j : Fin 4,
        Real.sqrt (coefficients U c s Q p.c0 t V left.height i*
          coefficients U c s Q p.c0 t V right.height j) := by
  have hl := actual_costs_paid U c s ha hb η Dart Q hDart w t V hV p h g left
  have hr := actual_costs_paid U c s ha hb η Dart Q hDart w t V hV p h g right
  have hr0 := costs_nonneg U c s ha η Dart Q w t V hV p h right
  have hL := coefficients_nonneg U c s ha Q p.c0 t V left.height h.hc0 hV
  have hR := coefficients_nonneg U c s ha Q p.c0 t V right.height h.hc0 hV
  have hz0 := (zero_lt_one.trans h.hZ).le
  have hD : 0<(Dart.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDart)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply (Real.sqrt_le_sqrt (mul_le_mul (hl i) (hr j) (hr0 j)
    (mul_nonneg (div_nonneg (hL i) hD.le) (Real.rpow_nonneg hz0 _)))).trans_eq
  have he : (coefficients U c s Q p.c0 t V left.height i/(Dart.absNorm:ℝ)*p.Z^p.loss)*
      (coefficients U c s Q p.c0 t V right.height j/(Dart.absNorm:ℝ)*p.Z^p.loss)=
      (coefficients U c s Q p.c0 t V left.height i*coefficients U c s Q p.c0 t V right.height j)*
        (p.Z^p.loss/(Dart.absNorm:ℝ))^2 := by ring
  rw [he,Real.sqrt_mul (mul_nonneg (hL i) (hR j)),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (div_nonneg (Real.rpow_nonneg hz0 _) hD.le)]
  ring

end
end Candidate.SilPrior.FourthPower.MixedFirstPaidCosts

namespace Candidate.SilPrior.FourthPower.MixedFirstPaidCosts
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSectorLocalization
open MixedFirstExceptionalApplication

/-- M is a fixed upper bound for the actual exceptional norm exponent.
The latter may depend on the subsequently chosen small epsilon; the
actual exponent is retained in Parameters and is never replaced by M. -/
def lossStep (M BG BX loss : ℝ) : ℝ :=
  min (1/100) (loss/(100*(1+M+BG+BX)))

theorem lossStep_pos (M BG BX loss : ℝ) (hM : 0 ≤ M)
    (hBG : 0 ≤ BG) (hBX : 0 ≤ BX) (hloss : 0 < loss) :
    0 < lossStep M BG BX loss := by
  unfold lossStep
  exact lt_min (by norm_num) (div_pos hloss (by positivity))

theorem lossStep_le (M BG BX loss : ℝ) : lossStep M BG BX loss ≤ 1/100 :=
  min_le_left _ _

/-- All four losses are paid at once, uniformly for every actual
exceptional norm exponent between zero and the fixed upper bound. -/
theorem lossStep_budgets (M BG BX loss : ℝ) (hM : 0 ≤ M)
    (hBG : 0 ≤ BG) (hBX : 0 ≤ BX) (hloss : 0 < loss)
    (Bnorm : ℝ) (hBnorm : 0 ≤ Bnorm) (hBM : Bnorm ≤ M) :
    let h := lossStep M BG BX loss
    BG*h+BX*h+3*h+3*h ≤ loss ∧
      2*h+(BG+1)*h ≤ loss ∧
      3*h+(2*Bnorm+BG)*h+7*h/3+5*(3*h)/6 ≤ loss ∧
      BG*(1+h)-(2*BG+1) ≤ loss := by
  dsimp only
  let h := lossStep M BG BX loss
  have hh : 0 < h := lossStep_pos M BG BX loss hM hBG hBX hloss
  have hh1 : h ≤ 1/100 := lossStep_le M BG BX loss
  have hden : 0 < 100*(1+M+BG+BX) := by positivity
  have hsmall : h*(100*(1+M+BG+BX)) ≤ loss :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hMh := mul_nonneg hM hh.le
  have hBGh := mul_nonneg hBG hh.le
  have hBXh := mul_nonneg hBX hh.le
  have hBactual := mul_le_mul_of_nonneg_right hBM hh.le
  have htail : BG*h ≤ BG := by
    exact (mul_le_mul_of_nonneg_left (show h ≤ 1 by linarith) hBG).trans_eq (mul_one BG)
  change BG*h+BX*h+3*h+3*h ≤ loss ∧
    2*h+(BG+1)*h ≤ loss ∧
    3*h+(2*Bnorm+BG)*h+7*h/3+5*(3*h)/6 ≤ loss ∧
    BG*(1+h)-(2*BG+1) ≤ loss
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The fixed exponents are selected BEFORE the small losses. Both
actual cutoff exponents and actual normExponent remain unchanged in
their later applications; these are only uniform upper bounds. -/
theorem fixed_coarse_exponents (B ξfirst ξsecond κ L Pexp ε : ℝ)
    (hξfirst : ξfirst ≤ 1) (hξsecond : ξsecond ≤ 1) (hκ : κ ≤ 1)
    (hL : 0 ≤ L) (hPexp : 0 ≤ Pexp) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MixedFirstCutoffs.childExponent B ξfirst κ ≤ 8*B+3 ∧
      MixedFirstCutoffs.tailExponent B ξfirst κ ≤ 25*B+5 ∧
      MixedFirstCutoffs.geometryExponent B ξsecond ≤ 17*B+3 ∧
      0 ≤ normExponent L Pexp ε ∧ normExponent L Pexp ε ≤ 2*L+Pexp+1 := by
  unfold MixedFirstCutoffs.tailExponent MixedFirstCutoffs.geometryExponent
    MixedFirstCutoffs.secondExponent MixedFirstCutoffs.childExponent normExponent
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Literal parameters for the padded selected-volume average. The
cutoff supplied by MixedFirstCutoffs is the exact first nominal scale,
so Cfirst is one. The five small positive parameters share one step. -/
def chosenParameters (M BG BX loss Bnorm R P S d l c0 Z Kfirst Tfirst W : ℝ) : Parameters where
  Z := Z
  Kfirst := Kfirst
  Tfirst := Tfirst
  Cfirst := 1
  ξfirst := lossStep M BG BX loss
  κpad := lossStep M BG BX loss
  W := W
  ε := lossStep M BG BX loss
  δ := lossStep M BG BX loss
  Bnorm := Bnorm
  BG := BG
  BX := BX
  R := R
  P := P
  S := S
  d := d
  l := l
  c0 := c0
  omega := lossStep M BG BX loss
  sigma := 3*lossStep M BG BX loss
  loss := loss
  saving := 2*BG+1

/-- The threshold precedes every actual slot pool, selected subset,
source scale and actual Bnorm. There is no slot-by-slot loss and no
lower bound on an individual slot width. The supplied reference may
be the fixed subunit uncentered reference, since only c0>0 is required.

The exceptional gap is the genuine inner requirement alpha+2delta<1
at alpha=7/10. The same step can be used for xi_second and epsilon_cap;
fixed_coarse_exponents supplies their independent coarse enclosures. -/
theorem uniform_actual_gates (N : ℕ) (M BG BX loss R P S d l c0 : ℝ)
    (hM : 0 ≤ M) (hBG : 0 ≤ BG) (hBX : 0 ≤ BX) (hloss : 0 < loss)
    (hS : 0 ≤ S) (hd : 0 ≤ d) (hc0 : 0 < c0)
    (hmixed : P+2*S+4*d < R) (hnative : (3/4:ℝ)*S < d)
    (href : ReferenceChoice R P S d l) :
    0 < lossStep M BG BX loss ∧ lossStep M BG BX loss ≤ 1/100 ∧
      (7/10:ℝ)+2*lossStep M BG BX loss < 1 ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀(α : Type u) [Fintype α], ∀q : MixedSupplierFourthRow.Data α,
        Fintype.card α ≤ N → (∀i,0 < q.P i) →
        MixedSelectedVolume.volume q = Z^d →
      ∀Bnorm : ℝ, 0 ≤ Bnorm → Bnorm ≤ M →
      ∀Kfirst Tfirst : ℝ, 0 < Kfirst →
        Gates (chosenParameters M BG BX loss Bnorm R P S d l c0 Z Kfirst Tfirst
          (MixedSelectedVolume.scale q)) := by
  let h := lossStep M BG BX loss
  have hh : 0 < h := lossStep_pos M BG BX loss hM hBG hBX hloss
  have hh1 : h ≤ 1/100 := lossStep_le M BG BX loss
  refine ⟨hh,hh1,by linarith,?_⟩
  have hcap : ∀ᶠ Z : ℝ in atTop, max (4:ℝ) ((2:ℝ)^N) ≤ Z^h :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hh)) _
  filter_upwards [hcap,Filter.eventually_gt_atTop (1:ℝ)] with Z hcap hZ
  refine ⟨hZ,?_⟩
  intro α instα q hN hP hvolume Bnorm hBnorm hBM Kfirst Tfirst hK
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hpad : MixedSelectedVolume.padding q ≤ Z^h :=
    (MixedSelectedVolume.padding_le q N hN).trans ((le_max_right _ _).trans hcap)
  have hfour : (4:ℝ) ≤ Z^h := (le_max_left _ _).trans hcap
  have hlog := Real.logb_le_logb_of_le hZ (by norm_num : (0:ℝ)<4) hfour
  rw [Real.logb_rpow hz hZ.ne'] at hlog
  have hfrequency : frequencyLoss Z 1 h+h ≤ 3*h := by
    unfold frequencyLoss
    simp only [mul_one]
    linarith
  have hW := actual_padding_gates q hP Z d h hZ hvolume hpad
  have hb := lossStep_budgets M BG BX loss hM hBG hBX hloss Bnorm hBnorm hBM
  dsimp only at hb
  exact {
    hZ := hZ
    hK := hK
    hW := MixedSelectedVolume.scale_pos q hP
    hc0 := hc0
    hCfirst := le_refl 1
    hξ := hh.le
    hε := hh.le
    hδ := hh.le
    hS := hS
    hd := hd
    mixed := hmixed
    native := hnative
    reference := href
    Wlower := hW.1
    Wupper := hW.2
    frequency := hfrequency
    zero_loss := hb.1
    native_loss := hb.2.1
    exceptional_loss := hb.2.2.1
    tail_loss := hb.2.2.2 }

end
end Candidate.SilPrior.FourthPower.MixedFirstPaidCosts
