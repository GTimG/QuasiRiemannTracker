/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All polynomial and positivity gates for the actual initial first budget follow
from the global face and long-reference scales. Thresholds precede moving data. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalResidualCap
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialTruncated
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic
open QRH.Record1252270103Low QRH.Record1252270103Source.InitialPhysical
local notation "O"=>HeckeFamily.O

section Positivity
variable {ι:Type*}[Fintype ι]
variable (rayM:Ideal O)[NeZero rayM]
variable (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
variable (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z:ℝ)(hZ:1<Z)(η η₀:Character)(R₀:Ideal O)
variable (θ:ι→RayQuotient.Characters rayM H)(w v:ι→ℝ)(t:ℝ)
variable (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
variable (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

theorem initial_long_positive (hw:∀i,0≤w i)(hy₂:1≤Y₂)(hl₁:Y₂≤X₁)(hl₂:Y₂≤X₂) :
    0<sourceRadius s ∧ 1≤volume s := by
  have hZ0:=zero_lt_one.trans hZ
  have hspos:0<sourceRadius s:=by
    rw [initial_source_radius_identity rayM H hH W hW hsW Z hZ0 η η₀ R₀ θ w v t p
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod]
    exact mul_pos (mul_pos (pow_pos (by norm_num) _) (sq_pos_of_pos (by norm_num))) (volume_pos s)
  have hvlo:1≤volume s:=by
    have hp:1≤X₁*X₂:=by
      simpa using mul_le_mul (hy₂.trans hl₁) (hy₂.trans hl₂) (by norm_num : (0:ℝ)≤1) hX₁.le
    have hs:1≤Z^(∑i,w i):=Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
    change 1≤CenteredMomentExceptionalAmplitudePair.volume (s).toData
    rw [initialInput_volume rayM H hH W hW hsW Z hZ0 η η₀ R₀ θ w v t p
      (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod]
    simpa using mul_le_mul hp hs (by norm_num : (0:ℝ)≤1) (mul_pos hX₁ hX₂).le
  exact ⟨hspos,hvlo⟩
end Positivity

section Pointwise
variable {ι:Type*}[Fintype ι]
variable (rayM:Ideal O)[NeZero rayM]
variable (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
variable (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z:ℝ)(hZ:1<Z)(η η₀:Character)(R₀:Ideal O)
variable (θ:ι→RayQuotient.Characters rayM H)(w v:ι→ℝ)(t:ℝ)
variable (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
variable (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

theorem initial_caps_pointwise (N:ℕ)(B lam cap:ℝ)(hB:B≤1)(hlam:1≤lam)(hcap:cap≤1)
    (hN:Fintype.card ι≤N)(hw:∀i,0≤w i)
    (hadm:(globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hy₂:1≤Y₂)(hl₁:Y₂≤X₁)(hl₂:Y₂≤X₂)
    (hrad:(2:ℝ)^N*(9/4)^2*Z≤Z^(2:ℝ))
    (hpool:(2:ℝ)^N*(9/4)^2*Z^(3:ℝ)≤Z^(4:ℝ)) :
    0<sourceRadius s ∧ sourceRadius s≤Z^(2:ℝ) ∧ 1≤volume s ∧ volume s≤Z ∧
      ∀I∈finiteColumns (Fintype.piFinset (s).pools),(I.absNorm:ℝ)≤Z^(4:ℝ) := by
  have hZ0:=zero_lt_one.trans hZ
  have hpositive:=initial_long_positive rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hw hy₂ hl₁ hl₂
  have hscap:=initial_source_radius_cap rayM H hH W hW hsW Z hZ0 η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N hN B lam cap hZ hB hlam hw hadm
  have hvhi:=initial_volume_cap rayM H hH W hW hsW Z hZ0 η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod B lam cap hZ hB hlam hw hadm
  refine ⟨hpositive.1,hscap.trans hrad,hpositive.2,hvhi,?_⟩
  intro I hI
  exact (initial_full_column_cap_of_global_face rayM H hH W hW hsW Z hZ0 η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N hN B lam cap hZ hB (zero_le_one.trans hlam) hcap
    hw hadm hy₂ hl₁ hl₂ I hI).trans hpool

end Pointwise

theorem eventually_initial_caps (N:ℕ)(B lam cap:ℝ)(hB:B≤1)(hlam:1≤lam)(hcap:cap≤1) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{ι:Type*}[Fintype ι](rayM:Ideal O)[NeZero rayM]
      (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
      (η η₀:Character)(R₀:Ideal O)(θ:ι→RayQuotient.Characters rayM H)(w v:ι→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
      Fintype.card ι≤N→(∀i,0≤w i)→
      (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
      1≤Y₂→Y₂≤X₁→Y₂≤X₂→
      let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
        p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
      0<sourceRadius s ∧ sourceRadius s≤Z^(2:ℝ) ∧ 1≤volume s ∧ volume s≤Z ∧
        ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ) := by
  filter_upwards [eventual_radius_absorption N 1 (by norm_num),eventual_full_pool_absorption N]
    with Z hradius hpool
  refine ⟨hradius.1,?_⟩
  intro hZ ι instι rayM instRay H hH W hW hsW η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hadm hy₂ hl₁ hl₂ s
  apply initial_caps_pointwise rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N B lam cap hB hlam hcap hN hw hadm hy₂ hl₁ hl₂
  · convert hradius.2 using 1 <;> norm_num
  · exact hpool.2

end
end QRH.Record1252270103Source.InitialTruncated
#print axioms QRH.Record1252270103Source.InitialTruncated.eventually_initial_caps

#print axioms QRH.Record1252270103Source.InitialTruncated.initial_long_positive

#print axioms QRH.Record1252270103Source.InitialTruncated.initial_caps_pointwise
