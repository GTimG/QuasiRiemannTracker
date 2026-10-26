/- Copyright (c) 2026 Sil. Apache-2.0.
Generic raw reference and exact first-scale cancellation. No restored-root
constructor or choice of ordinary reference is imported here.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshDeclaredMass
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshSelectedKernel
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstGeometricCaps

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedRawReference
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentFiniteProfileExceptional OuterFreshRootAdmission
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondWindowBudget
open MixedPrincipalPair MixedSupplierFourthRow MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstProfileEnvelope
open MixedInnerExceptionalBlock MixedFirstExceptionalNormalization
open OuterFreshSelected OuterFreshCutoffAllowance OuterFreshDeclaredMass
open OuterFreshAllocationMass OuterFreshSelectedKernel
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def referenceBase (τ : Character) (C : Id) (V : ℝ) : ℝ :=
  (τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2/fixedPresentationCost

theorem referenceBase_nonneg (τ : Character) (C : Id) (V : ℝ) : 0≤referenceBase τ C V :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) fixedPresentationCost_pos.le
def profileCore (r:Source ι a b)(Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ tp V:ℝ) : ℝ :=
  Kslot^(2*N)*(sourceControl control r.W₁*sourceControl control r.W₂)^2*
    (height t₀ V r.t₁ r.t₂)^degree*
    (CenteredMomentSecondWindowBudget.profileMoment degree)^2*heightEnvelope tp^(2*degree)

theorem profileCore_nonneg (r:Source ι a b)(Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ tp V:ℝ)(hK:0≤Kslot)(hV:0≤V) : 0≤profileCore r Kslot N degree control t₀ tp V := by
  have hh:0≤height t₀ V r.t₁ r.t₂:=by unfold height;positivity
  have ht:0≤heightEnvelope tp:=(heightEnvelope_pos tp).le
  unfold profileCore
  positivity

theorem angleEnvelope_factor (r:Source ι a b)(Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))
    (t₀ tp V Z Rdecl ε:ℝ) :
    angleEnvelope r 1 Kslot N degree control t₀ tp V Z Rdecl ε=
      profileCore r Kslot N degree control t₀ tp V*(Z^Rdecl/fixedPresentationCost)*Z^ε := by
  unfold angleEnvelope profileBase profileCore
  ring

def firstReference (q:Data ι)(τ:Character)(C:Id)(V:ℝ) : ℝ :=
  (τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2/
    (fixedPresentationCost*frozenVolume q*(selectedVolume q)^2)

theorem firstReference_nonneg (q:Data ι)(hP:∀i,0<q.P i)(τ:Character)(C:Id)(V:ℝ) :
    0≤firstReference q τ C V := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (mul_nonneg (mul_nonneg fixedPresentationCost_pos.le (frozenVolume_pos q hP).le) (sq_nonneg _))

/-- Exact multiplicative form of the checked original nominal logarithm.
Both full first common norms remain present until the next cancellation. -/
theorem nominal_equality (η τ:Character)(C D:Id)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V=
      (τ.modulus.absNorm:ℝ)*V^2/
        (fixedPresentationCost*(η.modulus.absNorm:ℝ)*K*(C.absNorm:ℝ)*(D.absNorm:ℝ)) := by
  have hz:=zero_lt_one.trans hZ
  have hη:=zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  have hτ:=zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hCN:=zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hDN:=zero_lt_one.trans_le (ideal_norm_one_le hD.1)
  have hnom:=firstNominalScale_pos C D _ (subsetGenerator_supported C D hC E).1 K V hK hV
  have hinput:Z^(inputWidth η K Z)=K*(η.modulus.absNorm:ℝ)*fixedPresentationCost := by
    unfold inputWidth
    rw [Real.rpow_add hz,Real.rpow_add hz]
    simp only [Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hη,
      Real.rpow_logb hz hZ.ne' fixedPresentationCost_pos]
  have hVpow:Z^(2*Real.logb Z V)=V^2 := by
    rw [two_mul,Real.rpow_add hz]
    simp only [Real.rpow_logb hz hZ.ne' hV,pow_two]
  have he:=congrArg (fun x:ℝ=>Z^x) (actual_nominal_log η τ C D hC hD hCD E K V Z hK hV hZ hmod)
  rw [Real.rpow_logb hz hZ.ne' hnom] at he
  rw [he,Real.rpow_sub hz,Real.rpow_sub hz,Real.rpow_sub hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' hτ,hVpow,hinput,
    Real.rpow_logb hz hZ.ne' hCN,Real.rpow_logb hz hZ.ne' hDN]
  ring

/-- The dyadic first frequency cancels against deficit, as does the
positive-part completion. No retained-frequency inequality is needed. -/
theorem child_deficit_exact (C D:Id)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(K V Z θ:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(n:ℤ) :
    nominalChildScale C D E K V Z θ n*
      Z^(deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)-
        max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+3*θ)=
      ((D.absNorm:ℝ)*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V/(C.absNorm:ℝ))*Z^(4*θ) := by
  have hz:=zero_lt_one.trans hZ
  have hCN:=zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hDN:=zero_lt_one.trans_le (ideal_norm_one_le hD.1)
  have hnom:=firstNominalScale_pos C D _ (subsetGenerator_supported C D hC E).1 K V hK hV
  rw [nominalChildScale,←Real.rpow_add hz]
  have hexp:(Real.logb Z (dyadicScale n)+max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+θ)+
      (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)-
        max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+3*θ)=
      Real.logb Z (D.absNorm:ℝ)+Real.logb Z
        (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V)-
          Real.logb Z (C.absNorm:ℝ)+4*θ := by
    unfold deficit
    ring
  rw [hexp,Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' hCN,Real.rpow_logb hz hZ.ne' hDN,Real.rpow_logb hz hZ.ne' hnom]

/-- The precise scalar used by the ORIGINAL first child. This removes
all second common/unit factors and the original eta/K, while retaining
the full first common denominator, frozen volume and selected volume. -/
theorem first_declared_exact (q:Data ι)(hP:∀i,0<q.P i)
    (η τ:Character)(C₁ D₁:Id)(hC₁:Supported C₁)(hD₁:Supported D₁)
    (hCD₁:CompletedGauss.primeSupport C₁=CompletedGauss.primeSupport D₁)(E₁:Finset (CommonIndex C₁ D₁))
    (K V Z θ:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C₁ D₁=>P.val) E₁*activeConductor C₁ D₁})
    (n:ℤ)(C₂ D₂:Id)(hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂)) :
    nominalChildScale C₁ D₁ E₁ K V Z θ n*normalizer C₂ D₂ U*
      (Z^(declaredWidth q η K Z (deficit C₁ D₁ E₁ K V Z n)
        (Real.logb Z (C₁.absNorm:ℝ)) θ C₂ D₂ U)/fixedPresentationCost)=
      ((τ.modulus.absNorm:ℝ)*(V/(C₁.absNorm:ℝ))^2/
        (fixedPresentationCost*frozenVolume q*(selectedVolume q)^2))*Z^(4*θ) := by
  have hf:=frozenVolume_pos q hP
  have hs:0<selectedVolume q:=Finset.prod_pos (fun i _=>hP i.val.val)
  have hη:=zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  have hCN:=zero_lt_one.trans_le (ideal_norm_one_le hC₁.1)
  have hDN:=zero_lt_one.trans_le (ideal_norm_one_le hD₁.1)
  rw [mul_assoc,normalizer_paid_declared_width q hP η K Z
    (deficit C₁ D₁ E₁ K V Z n) (Real.logb Z (C₁.absNorm:ℝ)) θ hK hZ C₂ D₂ hC₂ U]
  calc
    _=((η.modulus.absNorm:ℝ)*K/(frozenVolume q*(selectedVolume q)^2))*
      (nominalChildScale C₁ D₁ E₁ K V Z θ n*
        Z^(deficit C₁ D₁ E₁ K V Z n-Real.logb Z (C₁.absNorm:ℝ)-
          max (deficit C₁ D₁ E₁ K V Z n-Real.logb Z (C₁.absNorm:ℝ)) 0+3*θ)) := by ring
    _=_:=by
      rw [child_deficit_exact C₁ D₁ hC₁ hD₁ E₁ K V Z θ hK hV hZ n,
        nominal_equality η τ C₁ D₁ hC₁ hD₁ hCD₁ E₁ K V Z hK hV hZ hmod]
      field_simp [hη.ne',hK.ne',hCN.ne',hDN.ne',fixedPresentationCost_pos.ne',hf.ne',hs.ne']
      <;> ring

/-- Fixed-profile numerator left after sharp support cancels the ordinary
prefix. It contains no live-volume factor. -/
def rawProfileRoot (s : Source ι a b) : ℝ :=
  ((∏i,s.M i)^4*(2:ℝ)^Fintype.card ι)/a^2

theorem rawProfileRoot_nonneg (s : Source ι a b) : 0≤rawProfileRoot s := by
  unfold rawProfileRoot
  positivity

end
end Candidate.FourthPower.RepairedRawReference

