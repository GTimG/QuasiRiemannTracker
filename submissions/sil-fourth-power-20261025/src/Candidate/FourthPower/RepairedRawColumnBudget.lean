/- Copyright (c) 2026 Sil. Apache-2.0.
Sharp original lower column support must be retained until RAW source
reconstruction. Merely replacing both column scales by one is valid but
loses one growing sourceVolume at the next first-Poisson consumer.

-/
import Candidate.FourthPower.RepairedRawReference
import Candidate.FourthPower.OuterFreshAssembly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRawColumnBudget
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge
open ActualEisensteinCubic
open CenteredMomentHeckeColumnWindow MixedSupplierOriginalFrequency
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentSecondWindowBudget CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSourceBlockWindows
open MixedPrincipalPair MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedFirstProfileEnvelope MixedFirstExceptionalNormalization
open OuterFreshWindowPair OuterFreshRows OuterFreshAssembly OuterFreshConsumer
open OuterFreshAllocationMass OuterFreshSelectedKernel OuterFreshSelected
open OuterFreshRootAdmission OuterFreshCutoffAllowance OuterFreshDeclaredMass
open RepairedRawReference
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι:Type u}[Fintype ι]{κ:Type v}[Fintype κ]{a b:ℝ}

theorem common_factor (C E:Id)(hC:C≠0)(hE:E≠0)(R δ:ℝ)(hR:0≤R) :
    Real.sqrt (((C.absNorm:ℝ)^δ*(R/(C.absNorm:ℝ)))*((E.absNorm:ℝ)^δ*(R/(E.absNorm:ℝ))))=
      R*Real.sqrt ((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)/Real.sqrt ((C.absNorm:ℝ)*E.absNorm) := by
  have hc:0<(C.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hC)
  have he:0<(E.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hE)
  have hid:((C.absNorm:ℝ)^δ*(R/(C.absNorm:ℝ)))*((E.absNorm:ℝ)^δ*(R/(E.absNorm:ℝ)))=
      (R^2*((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ))/((C.absNorm:ℝ)*E.absNorm) := by
    field_simp [hc.ne',he.ne']
    <;> ring
  rw [hid,Real.sqrt_div (mul_nonneg (sq_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg he.le _))),
    Real.sqrt_mul (sq_nonneg R),Real.sqrt_sq_eq_abs,abs_of_nonneg hR]

theorem outer_common_factor (C E:Id)(hC:C≠0)(hE:E≠0)(K R δ:ℝ)(hR:0≤R)(n:Fin 4→ℤ) :
    outerScalar C E K n*
      Real.sqrt (((C.absNorm:ℝ)^δ*(R/(C.absNorm:ℝ)))*((E.absNorm:ℝ)^δ*(R/(E.absNorm:ℝ))))=
      (K*R*Real.sqrt ((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ))/
        (((C.absNorm:ℝ)*E.absNorm)*Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3))) := by
  have hc:0<(C.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hC)
  have he:0<(E.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hE)
  have hce:0<Real.sqrt ((C.absNorm:ℝ)*E.absNorm):=Real.sqrt_pos.mpr (mul_pos hc he)
  have hx:0<Real.sqrt (dyadicScale (n 2)):=Real.sqrt_pos.mpr (dyadicScale_pos _)
  have hy:0<Real.sqrt (dyadicScale (n 3)):=Real.sqrt_pos.mpr (dyadicScale_pos _)
  rw [common_factor C E hC hE R δ hR,outerScalar,←Real.sqrt_mul hc.le]
  calc
    _=(K*R*Real.sqrt ((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ))/
        ((Real.sqrt ((C.absNorm:ℝ)*E.absNorm))^2*Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3))) := by
      field_simp [hce.ne',hx.ne',hy.ne']
      <;> ring
    _=_:=by rw [Real.sq_sqrt (mul_nonneg hc.le he.le)]

theorem common_subpowers (C E:Id)(hC:C≠0)(hE:E≠0)(Z B δ:ℝ)
    (hZ:1≤Z)(hδ:0≤δ)(hc:(C.absNorm:ℝ)≤Z^B)(he:(E.absNorm:ℝ)≤Z^B) :
    Real.sqrt ((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)≤Z^(2*B*δ) := by
  have hCN:=ideal_norm_one_le hC
  have hEN:=ideal_norm_one_le hE
  have hnorm:1≤(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ:=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hCN hδ) (Real.one_le_rpow hEN hδ)
  have hz:=zero_lt_one.trans_le hZ
  have hc':(C.absNorm:ℝ)^δ≤Z^(B*δ):=by
    simpa only [←Real.rpow_mul hz.le] using Real.rpow_le_rpow (Nat.cast_nonneg _) hc hδ
  have he':(E.absNorm:ℝ)^δ≤Z^(B*δ):=by
    simpa only [←Real.rpow_mul hz.le] using Real.rpow_le_rpow (Nat.cast_nonneg _) he hδ
  have hs:Real.sqrt ((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)≤(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ := by
    have hh:=Real.sqrt_le_sqrt (le_mul_of_one_le_right (zero_le_one.trans hnorm) hnorm)
    simpa only [←pow_two,Real.sqrt_sq_eq_abs,abs_of_nonneg (zero_le_one.trans hnorm)] using hh
  apply hs.trans
  apply (mul_le_mul hc' he' (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hz.le _)).trans_eq
  rw [←Real.rpow_add hz]
  congr 1
  ring

theorem common_height_norm (τ:Character)(t:ℝ)(C E:Id)(hC:C≠0)(hE:E≠0) :
    ‖heightCoeff τ t C*star (heightCoeff τ t E)‖≤1 := by
  rw [norm_mul,norm_star]
  exact (mul_le_mul (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ t C hC)
    (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ t E hE)
    (norm_nonneg _) zero_le_one).trans_eq (by ring)

/-- This is coefficient support, valid for the actual selected-dependent
keep and natural-zero coefficient. No untwisted-block nonzero inference. -/
theorem actual_outer_column_scales (q:Data ι)(x:Frozen q)(y:Selected q)
    (r:Source (RestIndex q) a b)(ha:0<a)(hm:Matches q x r ha)
    (seed:Id)(τ:Character)(ξ:RayCharacter)(C E:Id)(hC:Supported C)(hE:Supported E)
    (U:Finset (CommonIndex C E))(tp R:ℝ)(rows:Finset O)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock τ tp (fixedPool q x r seed) (outerColumn q x y seed ξ)
      C E hC hE U R rows Φ K n≠0) :
    (a^2/pairNorm r.d)*sourceVolume r/(C.absNorm:ℝ)≤dyadicScale (n 2) ∧
      (a^2/pairNorm r.d)*sourceVolume r/(E.absNorm:ℝ)≤dyadicScale (n 3) := by
  have hl:=physicalBlock_scale_lower τ tp (fixedPool q x r seed) (outerColumn q x y seed ξ)
    C E hC hE U R rows Φ K n (a^2/pairNorm r.d) (sourceVolume r)
    (div_pos (sq_pos_of_pos ha) (pairNorm_pos r.hd.1 r.hd.2))
    (fun I hI=>(outer_lower_seed q x y r ha hm seed ξ I hI).1) hne
  constructor
  · have he:sourceVolume r/(C.absNorm:ℝ)*(a^2/pairNorm r.d)≤dyadicScale (n 2):=
      (le_div_iff₀ (div_pos (sq_pos_of_pos ha) (pairNorm_pos r.hd.1 r.hd.2))).mp hl.1
    convert he using 1 <;> ring
  · have he:sourceVolume r/(E.absNorm:ℝ)*(a^2/pairNorm r.d)≤dyadicScale (n 3):=
      (le_div_iff₀ (div_pos (sq_pos_of_pos ha) (pairNorm_pos r.hd.1 r.hd.2))).mp hl.2
    convert he using 1 <;> ring

/-- The missing volume factor is recovered from the TWO actual lower
column scales. Common harmonic weight stays exactly 1/sqrt(NC*NE). -/
theorem sharp_pair_denominator (C E:Id)(hC:C≠0)(hE:E≠0)
    (X Y A V:ℝ)(hX:0<X)(hY:0<Y)(hA:0<A)(hV:0<V)
    (hl:A*V/(C.absNorm:ℝ)≤X)(hr:A*V/(E.absNorm:ℝ)≤Y) :
    1/(((C.absNorm:ℝ)*E.absNorm)*Real.sqrt X*Real.sqrt Y)≤
      (1/(A*V))*pairWeight C E := by
  have hc:0<(C.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hC)
  have he:0<(E.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hE)
  have hce:0<Real.sqrt ((C.absNorm:ℝ)*E.absNorm):=Real.sqrt_pos.mpr (mul_pos hc he)
  have hxy:((A*V)^2)/((C.absNorm:ℝ)*E.absNorm)≤X*Y:=by
    convert mul_le_mul hl hr (div_pos (mul_pos hA hV) he).le hX.le using 1 <;> ring
  have hs:=Real.sqrt_le_sqrt hxy
  rw [Real.sqrt_div (sq_nonneg (A*V)),Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos hA hV),Real.sqrt_mul hX.le] at hs
  have hden:(A*V)*Real.sqrt ((C.absNorm:ℝ)*E.absNorm)≤
      ((C.absNorm:ℝ)*E.absNorm)*Real.sqrt X*Real.sqrt Y := by
    have hh:=mul_le_mul_of_nonneg_left hs (mul_pos hc he).le
    have heq:((C.absNorm:ℝ)*E.absNorm)*((A*V)/Real.sqrt ((C.absNorm:ℝ)*E.absNorm))=
        (A*V)*Real.sqrt ((C.absNorm:ℝ)*E.absNorm) := by
      calc
        _=(A*V)*((Real.sqrt ((C.absNorm:ℝ)*E.absNorm))^2/
            Real.sqrt ((C.absNorm:ℝ)*E.absNorm)):=by
          rw [Real.sq_sqrt (mul_pos hc he).le]
          ring
        _=_:=by field_simp [hce.ne']
    rw [heq] at hh
    convert hh using 1 <;> ring
  have hb:=one_div_le_one_div_of_le (mul_pos (mul_pos hA hV) hce) hden
  convert hb using 1 <;> unfold pairWeight <;> ring

/-- rootFactor's ordinary prefix cancels the one forced by the true
lower column support. The source volume is retained in the denominator. -/
theorem root_factor_sharp (r:Source κ a b)(ha:0<a) :
    rootFactor r*(1/((a^2/pairNorm r.d)*sourceVolume r))=
      ((∏i,r.M i)^4*(2:ℝ)^Fintype.card κ)/(a^2*sourceVolume r) := by
  have hd:=pairNorm_pos r.hd.1 r.hd.2
  unfold rootFactor
  field_simp [hd.ne',ha.ne',(sourceVolume_pos r).ne']
  <;> ring

set_option maxHeartbeats 800000 in
/-- Original first-child dynamic factors cancel before the sharp
second-column support. This is the RAW-compatible replacement for the
coarser actual_block_budget_le; no block estimate is a premise. -/
theorem actual_block_sharp_budget_le (q:Data ι)(hP:∀i,0<q.P i)(r:Source κ a b)(ha:0<a)
    (η τ:Character)(C₁ D₁:Id)(hC₁:Supported C₁)(hD₁:Supported D₁)
    (hCD₁:CompletedGauss.primeSupport C₁=CompletedGauss.primeSupport D₁)(E₁:Finset (CommonIndex C₁ D₁))
    (K Vroot Z θ:ℝ)(hK:0<K)(hVroot:0<Vroot)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C₁ D₁=>P.val) E₁*activeConductor C₁ D₁})
    (n₁:ℤ)(C₂ D₂:Id)(hC₂:Supported C₂)(hD₂:Supported D₂)(U:Finset (CommonIndex C₂ D₂))
    (n₂:Fin 4→ℤ)
    (hx:(a^2/pairNorm r.d)*sourceVolume r/(C₂.absNorm:ℝ)≤dyadicScale (n₂ 2))
    (hy:(a^2/pairNorm r.d)*sourceVolume r/(D₂.absNorm:ℝ)≤dyadicScale (n₂ 3))
    (B δ εw εa Kslot:ℝ)(hδ:0≤δ)(hKslot:0≤Kslot)
    (hCcap:(C₂.absNorm:ℝ)≤Z^B)(hDcap:(D₂.absNorm:ℝ)≤Z^B)
    (N degree:ℕ)(control:Finset (ℕ×ℕ))(t₀ tp V:ℝ)(hV:0≤V) :
    let L:=nominalChildScale C₁ D₁ E₁ K Vroot Z θ n₁
    let Rdecl:=declaredWidth q η K Z (deficit C₁ D₁ E₁ K Vroot Z n₁)
      (Real.logb Z (C₁.absNorm:ℝ)) θ C₂ D₂ U
    (outerScalar C₂ D₂ L n₂*normalizer C₂ D₂ U)*
      (‖heightCoeff τ tp C₂*star (heightCoeff τ tp D₂)‖*
        (Z^εa*Real.sqrt (((C₂.absNorm:ℝ)^δ*(rootFactor r/(C₂.absNorm:ℝ)))*
          ((D₂.absNorm:ℝ)^δ*(rootFactor r/(D₂.absNorm:ℝ))))*
          angleEnvelope r 1 Kslot N degree control t₀ tp V Z Rdecl εw))≤
      (firstReference q τ C₁ Vroot*((∏i,r.M i)^4*(2:ℝ)^Fintype.card κ)/a^2*
        profileCore r Kslot N degree control t₀ tp V/sourceVolume r)*
        Z^(4*θ+εw+εa+2*B*δ)*pairWeight C₂ D₂ := by
  dsimp only
  let L:=nominalChildScale C₁ D₁ E₁ K Vroot Z θ n₁
  let Rdecl:=declaredWidth q η K Z (deficit C₁ D₁ E₁ K Vroot Z n₁)
    (Real.logb Z (C₁.absNorm:ℝ)) θ C₂ D₂ U
  let denom:=((C₂.absNorm:ℝ)*D₂.absNorm)*Real.sqrt (dyadicScale (n₂ 2))*Real.sqrt (dyadicScale (n₂ 3))
  let Hp:=‖heightCoeff τ tp C₂*star (heightCoeff τ tp D₂)‖
  let base:=firstReference q τ C₁ Vroot*rootFactor r*profileCore r Kslot N degree control t₀ tp V
  let cost:=1/((a^2/pairNorm r.d)*sourceVolume r)
  have hz:=zero_lt_one.trans hZ
  have hbase:0≤base:=mul_nonneg
    (mul_nonneg (firstReference_nonneg q hP τ C₁ Vroot) (rootFactor_nonneg r))
    (profileCore_nonneg r Kslot N degree control t₀ tp V hKslot hV)
  have hH:Hp≤1:=common_height_norm τ tp C₂ D₂ hC₂.1 hD₂.1
  have hpowers:=common_subpowers C₂ D₂ hC₂.1 hD₂.1 Z B δ hZ.le hδ hCcap hDcap
  have hden:1/denom≤cost*pairWeight C₂ D₂:=sharp_pair_denominator C₂ D₂ hC₂.1 hD₂.1 _ _
    (a^2/pairNorm r.d) (sourceVolume r) (dyadicScale_pos _) (dyadicScale_pos _)
    (div_pos (sq_pos_of_pos ha) (pairNorm_pos r.hd.1 r.hd.2)) (sourceVolume_pos r) hx hy
  have hden0:0≤1/denom:=by unfold denom;positivity
  have hpair:=mul_le_mul hpowers hden hden0 (Real.rpow_nonneg hz.le _)
  have hrad:=first_declared_exact q hP η τ C₁ D₁ hC₁ hD₁ hCD₁ E₁ K Vroot Z θ hK hVroot hZ hmod
    n₁ C₂ D₂ hC₂ U
  have heq:(outerScalar C₂ D₂ L n₂*normalizer C₂ D₂ U)*
      (Hp*(Z^εa*Real.sqrt (((C₂.absNorm:ℝ)^δ*(rootFactor r/(C₂.absNorm:ℝ)))*
        ((D₂.absNorm:ℝ)^δ*(rootFactor r/(D₂.absNorm:ℝ))))*
          angleEnvelope r 1 Kslot N degree control t₀ tp V Z Rdecl εw))=
      (Hp*(base*Z^(4*θ+εw+εa)))*
        (Real.sqrt ((C₂.absNorm:ℝ)^δ*(D₂.absNorm:ℝ)^δ)*(1/denom)) := by
    rw [angleEnvelope_factor]
    calc
      _=Hp*(profileCore r Kslot N degree control t₀ tp V)*
          (outerScalar C₂ D₂ L n₂*Real.sqrt (((C₂.absNorm:ℝ)^δ*(rootFactor r/(C₂.absNorm:ℝ)))*
            ((D₂.absNorm:ℝ)^δ*(rootFactor r/(D₂.absNorm:ℝ)))))*
          normalizer C₂ D₂ U*(Z^Rdecl/fixedPresentationCost)*Z^εw*Z^εa := by ring
      _=Hp*(profileCore r Kslot N degree control t₀ tp V)*rootFactor r*
          (L*normalizer C₂ D₂ U*(Z^Rdecl/fixedPresentationCost))*
          Z^εw*Z^εa*Real.sqrt ((C₂.absNorm:ℝ)^δ*(D₂.absNorm:ℝ)^δ)/denom := by
        rw [outer_common_factor C₂ D₂ hC₂.1 hD₂.1 L (rootFactor r) δ (rootFactor_nonneg r) n₂]
        dsimp only [denom]
        ring
      _=_ := by
        rw [hrad]
        dsimp only [base,firstReference]
        rw [Real.rpow_add hz,Real.rpow_add hz]
        ring
  rw [heq]
  have hfront:Hp*(base*Z^(4*θ+εw+εa))≤base*Z^(4*θ+εw+εa):=
    mul_le_of_le_one_left (mul_nonneg hbase (Real.rpow_nonneg hz.le _)) hH
  apply (mul_le_mul hfront hpair
    (mul_nonneg (Real.sqrt_nonneg _) hden0) (mul_nonneg hbase (Real.rpow_nonneg hz.le _))).trans_eq
  have hr:rootFactor r*cost=((∏i,r.M i)^4*(2:ℝ)^Fintype.card κ)/(a^2*sourceVolume r):=
    root_factor_sharp r ha
  calc
    _=(firstReference q τ C₁ Vroot*(rootFactor r*cost)*profileCore r Kslot N degree control t₀ tp V)*
        (Z^(4*θ+εw+εa)*Z^(2*B*δ))*pairWeight C₂ D₂:=by dsimp only [base];ring
    _=_:=by rw [hr,←Real.rpow_add hz];ring

end
end Candidate.FourthPower.RepairedRawColumnBudget

