/- Copyright (c) 2026 Sil. Apache-2.0.
The genuine second diagonal of the literal first residual source.
Both common and artificial full norm denominators are retained.
-/
import Candidate.FourthPower.MixedOriginalTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedOriginalSecondZero
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentLattice CenteredMomentTwist CenteredMomentSecondDiagonal
open CenteredMomentFirstAmplificationChoice EisensteinSchwartzPoisson
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedHeightEnergy MixedLiteralAllocation MixedCommonRestriction MixedCommonCoefficient
open MixedOriginalTail MixedOriginalNormCap MixedPoissonLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def originalTuple (s : Source ι a b) (ha : 0<a) (seed : Id) (v : Tuple ι) : ℂ :=
  tupleWeight (punctureProduct s.S s.H) v*
    profileCoefficient s.R s.ν s.Wslot s.P
      (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v

theorem original_tuple_norm (s : Source ι a b) (ha : 0<a) (seed : Id) (v : Tuple ι) :
    ‖originalTuple s ha seed v‖≤profileCap s := by
  have hp := profileCoefficient_norm_le s.R s.ν s.hν s.Wslot s.P s.M
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    (supControl s.W₁) (supControl s.W₂) (fun i=>zero_le_one.trans (s.hM i))
    (supControl_nonneg s.W₁) (supControl_nonneg s.W₂) s.hWnorm
    (fun x=>by simpa only [normPowerProfile_norm] using norm_le_supControl s.W₁ x)
    (fun x=>by simpa only [normPowerProfile_norm] using norm_le_supControl s.W₂ x)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v
  have hw : ‖tupleWeight (punctureProduct s.S s.H) v‖≤1 := by
    unfold tupleWeight
    split_ifs <;> norm_num
  rw [originalTuple,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans hp

/-- Uniform fiber bound for the actual original weighted column. No
coefficient envelope is an input; only the displayed numerical norm cap. -/
theorem original_column_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀(seed I : Id)(Y : ℝ),
      I≠0→1≤Y→(I.absNorm:ℝ)≤Y→‖sourceCoefficient s ha seed I‖≤C*profileCap s*Y^ε := by
  let δ := ε/(N+2:ℕ)
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδn : δ*(N+2:ℕ)=ε := by dsimp only [δ];push_cast;field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(1+D)^(N+2),by positivity,?_⟩
  intro ι instι a b s hcard ha seed I Y hI hY hNI
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hprofile : 0≤profileCap s := profileCap_nonneg s
  have hbase : 1≤(1+D)*Y^δ := by
    have hh := Real.one_le_rpow hY hδ.le
    nlinarith
  have hdiv : ((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
    (hd I hI).trans (mul_le_mul (by linarith)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hNI hδ.le) (by positivity) (by positivity))
  have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^ε := by
    rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
  have hf := finiteColumnCoefficient_norm_le (Fintype.piFinset (tuplePools s))
    (originalTuple s ha seed) (profileCap s) (profileCap_nonneg s)
    (fun v _ _=>original_tuple_norm s ha seed v) I hI
  change ‖sourceCoefficient s ha seed I‖≤_ at hf
  calc
    _ ≤ profileCap s*((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)^(Fintype.card ι+2) := hf
    _ ≤ profileCap s*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
    _ ≤ profileCap s*((1+D)*Y^δ)^(N+2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) (profileCap_nonneg s)
    _ = _ := by rw [hp];ring

def originalResidual (s : Source ι a b) (ha : 0<a) (seed G D : Id) (I : Id) : ℂ :=
  if D∣I then sourceCoefficient s ha seed (G*I) else 0

/-- The exact common-restricted pool of the first physical side.
The old seed is inside sourceCoefficient; D is the artificial divisor. -/
theorem original_residual_second_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀(seed Ccommon G D : Id)(hG : G≠0),D≠0→
      ∀(η : Character)(t Y : ℝ),1≤Y→sourceNormCap s.P b s.T s.d≤Y→
      ‖sourceSecondZero (CenteredMomentFirstPhysicalSource.columns Ccommon G hG (sourceColumns s))
        (originalResidual s ha seed G D) η t‖≤
      C*(profileCap s)^2*Y^(1+ε)/((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by
  obtain ⟨C0,hC0,hbound⟩ := original_column_bound N (ε/2) (half_pos hε)
  refine ⟨128*C0^2,by positivity,?_⟩
  intro ι instι a b s hcard ha seed Ccommon G D hG hD η t Y hY hcap
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hGN : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  let Q := CenteredMomentFirstPhysicalSource.columns Ccommon G hG (sourceColumns s)
  let β := originalResidual s ha seed G D
  have hmask (I : Id) (hi : β I≠0) : D∣I ∧ sourceCoefficient s ha seed (G*I)≠0 := by
    by_cases hDI : D∣I
    · exact ⟨hDI,by simpa only [β,originalResidual,if_pos hDI] using hi⟩
    · exact False.elim (hi (by simp only [β,originalResidual,if_neg hDI]))
  have hwhole (I : Id) (hi : β I≠0) : G*I≠0 ∧ ((G*I).absNorm:ℝ)≤Y := by
    have hh := original_coefficient_cap s ha seed (G*I) (hmask I hi).2
    exact ⟨hh.1,hh.2.trans hcap⟩
  have hcoeff (I : Id) (hI : I∈supportedColumns Q) (hi : β I≠0) :
      ‖β I‖≤C0*profileCap s*Y^(ε/2) := by
    dsimp only [β,originalResidual]
    rw [if_pos (hmask I hi).1]
    exact hbound ι a b s hcard ha seed (G*I) Y (hwhole I hi).1 hY (hwhole I hi).2
  have hsize (I : Id) (hI : I∈supportedColumns Q) (hi : β I≠0) :
      (I.absNorm:ℝ)≤Y/(G.absNorm:ℝ) := by
    apply (le_div_iff₀ hGN).mpr
    simpa only [map_mul,Nat.cast_mul,mul_comm] using (hwhole I hi).2
  have hh := sourceSecondZero_divisor_bound Q β η t (C0*profileCap s*Y^(ε/2))
    (Y/(G.absNorm:ℝ)) (by have := profileCap_nonneg s;positivity)
    (div_nonneg hY0.le hGN.le) D hD hcoeff (fun I _ hi=>(hmask I hi).1) hsize
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  apply hh.trans_eq
  calc
    _ = (128*C0^2)*(profileCap s)^2*((Y^(ε/2))^2*Y)/
        ((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by ring
    _ = _ := by rw [hp]

theorem supported_zero_reindex (Q : Finset Id) (hQ : ∀I∈Q,Supported I)
    (gen : Q→O) (hgen : ∀I,Supported (Ideal.span {gen I}))
    (heq : ∀I,gen I=primaryGenerator (I:Id)) (β : Id→ℂ) (K W : ℝ) :
    zeroDensity Finset.univ gen hgen (fun I : Q=>β I) K W=
      zeroDensity Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q=>β I) K W := by
  let e : Q ≃ supportedColumns Q :=
    { toFun := fun I=>⟨I,Finset.mem_filter.mpr ⟨I.property,hQ I I.property⟩⟩
      invFun := fun I=>⟨I,(Finset.mem_filter.mp I.property).1⟩
      left_inv := fun I=>by rfl
      right_inv := fun I=>by rfl }
  unfold zeroDensity
  apply congrArg (fun E : ℂ=>((16*K*W^3:ℝ):ℂ)*paperRadialFourier ballProfile 0*E)
  unfold secondZeroEnergy
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [heq,sourceGenerator,e]
  rfl

/-- Literal second-zero density on the actual first physical residual pool.
The fourth-power scale and original averaging give 16 K W^3 exactly.
This is a local diagonal bound; no outer common-label sum is hidden. -/
theorem original_residual_zero_density (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀(seed Ccommon G D : Id)(hG : G≠0),D≠0→
      ∀(η : Character)(t Y K W : ℝ),1≤Y→sourceNormCap s.P b s.T s.d≤Y→0≤K→0≤W→
      let Q := CenteredMomentFirstPhysicalSource.columns Ccommon G hG (sourceColumns s)
      ‖zeroDensity Finset.univ
        (CenteredMomentFirstPhysicalSource.element Ccommon G hG (sourceColumns s))
        (CenteredMomentFirstPhysicalSource.element_supported Ccommon G hG (sourceColumns s))
        (fun I : Q=>originalResidual s ha seed G D I*heightCoeff η t I) K W‖≤
      (16*K*W^3)*‖paperRadialFourier ballProfile 0‖*
        (C*(profileCap s)^2*Y^(1+ε)/((G.absNorm:ℝ)*(D.absNorm:ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := original_residual_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι instι a b s hcard ha seed Ccommon G D hG hD η t Y K W hY hcap hK hW
  dsimp only
  have hh := hbound ι a b s hcard ha seed Ccommon G D hG hD η t Y hY hcap
  rw [supported_zero_reindex
    (CenteredMomentFirstPhysicalSource.columns Ccommon G hG (sourceColumns s))
    (fun I hI=>CenteredMomentFirstPhysicalSource.column_supported Ccommon G hG (sourceColumns s) ⟨I,hI⟩)
    (CenteredMomentFirstPhysicalSource.element Ccommon G hG (sourceColumns s))
    (CenteredMomentFirstPhysicalSource.element_supported Ccommon G hG (sourceColumns s))
    (fun _=>rfl) (fun I=>originalResidual s ha seed G D I*heightCoeff η t I) K W]
  change ‖((16*K*W^3:ℝ):ℂ)*paperRadialFourier ballProfile 0*
    sourceSecondZero _ (originalResidual s ha seed G D) η t‖≤_
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤16*K*W^3)]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

end
end Candidate.FourthPower.MixedOriginalSecondZero
