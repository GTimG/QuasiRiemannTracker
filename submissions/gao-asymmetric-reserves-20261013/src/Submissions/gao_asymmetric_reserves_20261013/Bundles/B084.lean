/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B054
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B071
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B072
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B082
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B083
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSelectedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceProfileMassUniform

/- BEGIN ORIGINAL MODULE Analytic.JointRefinedCommonReference ; sha256 75717882adf63fbe5d4291052f27b3602e7b663e263107571b2ae11e6956f11b -/
section


/-! Common-reference allocation summation with prime-dependent error
 defects. This accepts the refined actual error deficit without replacing
 it by a uniform scalar or paying a first-label count. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget
open CenteredMomentSourceLiveColumn CenteredMomentEnergyCanonicalAmplifiedColumn
local notation "O" => HeckeFamily.O
local notation "Ray" => RayFourExpansion.RayCharacter
local instance jointRefinedCommonReferenceDecEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem variable_error_power_reference_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(H:Fin 4→ℝ)(Kmain ell deficit paid saving rmain:ℝ)
    (Kerror rerror errorDeficit:elementPool P→Fin 3→Ray→ℝ)
    (hV:0< V)(hC:0< C)(hq:0< q)(hZ:0< Z):
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=> H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P) (i:Fin 3) (χ:Ray) (j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) (errorDeficit p i χ) paid saving (rerror p i χ) j;
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor H
        (mainCores q V C Z allowance Kmain ell deficit paid eps saving rmain)
        (fun p i χ=> errorCores p (errorIndex i+1) q V C Z allowance (Kerror p i χ)
          (errorDeficit p i χ) paid eps saving (rerror p i χ)) j := by
  dsimp only
  intro j
  rw [source_normalized_identity P mainFactor b V C q Z allowance eps N _ _ _ hV hC hq hZ j]
  congr 1
  unfold averagedCoefficients
  simp only [one_mul]
  rw [main_core_power]
  congr 2
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [error_core_power]
    simp only [Nat.add_sub_cancel]
    ring

theorem common_annular_variable_error_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0< a)(hb:1≤ b)(hε:0<ε):
    ∃Cb:ℝ,0< Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤ N→a≤ s.lower→s.upper≤ b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(H0 Z allowance:ℝ),0< H0→0< Z→
    ∀(P:Finset (Ideal O))(mainFactor:ℝ)(H:Fin 4→ℝ),0≤ mainFactor→(∀j,0≤ H j)→
    ∀(Kmain ell deficit paid saving rmain:ℝ),0≤ Kmain→
    ∀(Kerror rerror errorDeficit:elementPool P→Fin 3→Ray→ℝ),(∀p i χ,0≤ Kerror p i χ)→
    let q:ℝ:=τ.modulus.absNorm;
    let amain:=fun j=> H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) (errorDeficit p i χ) paid saving (rerror p i χ) j;
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,sourceCoefficients P mainFactor amain aerror (powers ε) j*
          (volume (child s C R B τ t))^(powers ε j))*
          CenteredMomentFirstChildProfileControl.mass (child s C R B τ t)^2)→
    (commonEnergy (original s R seed) C hC τ t L CenteredMomentFirstAnnularMajorant.profile H0).re≤
      reference q (volume s) (C.absNorm:ℝ) Z allowance*
        (Cb*CenteredMomentFirstChildProfileControl.mass s^2*
          ∑j,(C.absNorm:ℝ)^ε*(b^N)^(powers ε j)*
            averagedCoefficients P mainFactor H
              (mainCores q (volume s) (C.absNorm:ℝ) Z allowance Kmain ell deficit paid ε saving rmain)
              (fun p i χ=> errorCores p (errorIndex i+1) q (volume s) (C.absNorm:ℝ)
                Z allowance (Kerror p i χ) (errorDeficit p i χ) paid ε saving (rerror p i χ)) j):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_reference_powers N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L H0 Z allowance hH0 hZ
    P mainFactor H hmain hH Kmain ell deficit paid saving rmain hKmain Kerror rerror errorDeficit hKerror
  dsimp only
  intro hchildren
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hNC:0<(C.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hC.1
  have hcoeff:=source_coefficients_nonneg P mainFactor hmain
    (fun j=> H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain ell deficit paid saving rmain j)
    (fun p i χ j=> H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror p i χ) (errorDeficit p i χ) paid saving (rerror p i χ) j) (powers ε)
    (fun j=> mul_nonneg (hH j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZ.le hKmain j))
    (fun p i χ j=> mul_nonneg (hH j) (error_coefficients_nonneg _ _ _ _ _ _ _ _ _
      hq.le hZ.le (hKerror p i χ) j))
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L
    CenteredMomentFirstAnnularMajorant.profile H0 Z allowance hH0 hZ
    (fun z=> CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 _ (powers ε)
    hcoeff (powers_nonneg ε hε.le) hchildren
  apply hh.trans_eq
  unfold reference
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact variable_error_power_reference_identity P mainFactor b (volume s) (C.absNorm:ℝ)
    (τ.modulus.absNorm:ℝ) Z allowance ε N H Kmain ell deficit paid saving rmain Kerror rerror errorDeficit
    (volume_pos s) hNC hq hZ j

#print axioms variable_error_power_reference_identity
#print axioms common_annular_variable_error_reference_powers
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRefinedCommonReference -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondAbsoluteCutoff ; sha256 99e4e52a3b84e005cda8f472b2795740ca47a5055ff4ea7e82627806714840d5 -/
section


/-! The high estimate is needed only in the bounded Fourier region.
Outside it the literal source coefficient mass supplies the majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily RayFourExpansion CenteredMomentSectorLocalization CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

def secondProjectedJointValues {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (t : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (weight : α → ℂ)
    (scale θ u v : ℝ) : ℝ :=
  ∑ k ∈ labels, ∑ L ∈ Ds k,
    ‖(UniqueFactorizationMonoid.moebius L : ℂ)*((scale : ℂ)*weight k)‖ *
      ‖((s k).withProjector L).toKernelLabel.leftValue
        (t k+2*Real.pi*(u-θ)) (z k) (dyadicScale (n k 2))‖ *
      ‖((s k).withProjector L).toKernelLabel.rightValue
        (t k+2*Real.pi*(v-(-θ))) (z k) (dyadicScale (n k 3))‖

def secondProjectedAbsoluteEnvelope {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (n : α → Fin 4 → ℤ) (scale : ℝ) : ℝ :=
  scale*∑ k ∈ labels, ∑ L ∈ Ds k, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
    (s k).toKernelLabel.absoluteEnvelope (dyadicScale (n k 2)) (dyadicScale (n k 3))

/-- Only the coarse Fourier tail spends cardinality. The hypotheses are
literal finite source sizes, coefficient sizes and dyadic denominators. -/
theorem second_projected_absolute_power {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (n : α → Fin 4 → ℤ) (Z scale A B C D E F : ℝ)
    (hZ : 0 < Z) (hscale : 0 ≤ scale) (hscale' : scale ≤ Z^A)
    (hlabels : (labels.card : ℝ) ≤ Z^B)
    (hprojectors : ∀ k ∈ labels, ((Ds k).card : ℝ) ≤ Z^C)
    (hcolumns : ∀ k ∈ labels, ((s k).toKernelLabel.columns.card : ℝ) ≤ Z^D)
    (hcoeff : ∀ k ∈ labels, ∀ I ∈ (s k).toKernelLabel.columns,
      ‖(s k).toKernelLabel.beta I‖ ≤ Z^E)
    (hdyad : ∀ k ∈ labels,
      (Real.sqrt (dyadicScale (n k 2)))⁻¹ ≤ Z^F ∧
      (Real.sqrt (dyadicScale (n k 3)))⁻¹ ≤ Z^F) :
    secondProjectedAbsoluteEnvelope labels s Ds n scale ≤ Z^(A+B+C+2*F+2*(D+E)) := by
  have hmass (k) (hk : k ∈ labels) :
      sourceAbsoluteMass (s k).toKernelLabel.columns (s k).toKernelLabel.beta ≤ Z^(D+E) :=
    sourceAbsoluteMass_le_power _ _ Z D E hZ (hcolumns k hk) (hcoeff k hk)
  have hterm (k) (hk : k ∈ labels) (L : Ideal O) :
      ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
        (s k).toKernelLabel.absoluteEnvelope (dyadicScale (n k 2)) (dyadicScale (n k 3)) ≤
        Z^(2*F+2*(D+E)) := by
    have hh := hdyad k hk
    have hsq := pow_le_pow_left₀ (sourceAbsoluteMass_nonneg _ _) (hmass k hk) 2
    have he : (Z^F*Z^F)*(Z^(D+E))^2 = Z^(2*F+2*(D+E)) := by
      rw [← Real.rpow_two,← Real.rpow_mul hZ.le,← Real.rpow_add hZ,
        ← Real.rpow_add hZ]
      congr 1
      ring
    calc
      _ ≤ 1*(s k).toKernelLabel.absoluteEnvelope (dyadicScale (n k 2)) (dyadicScale (n k 3)) :=
        mul_le_mul_of_nonneg_right (CenteredMomentWholeDivisorShell.moebius_norm_le_one L)
          ((s k).toKernelLabel.absoluteEnvelope_nonneg _ _)
      _ ≤ (Z^F*Z^F)*(Z^(D+E))^2 := by
        simp only [one_mul,SecondKernelLabel.absoluteEnvelope]
        exact mul_le_mul (mul_le_mul hh.1 hh.2 (by positivity) (by positivity)) hsq
          (by positivity) (by positivity)
      _ = _ := he
  have hinner (k) (hk : k ∈ labels) :
      (∑ L ∈ Ds k, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
        (s k).toKernelLabel.absoluteEnvelope (dyadicScale (n k 2)) (dyadicScale (n k 3))) ≤
        Z^(C+(2*F+2*(D+E))) := by
    calc
      _ ≤ ((Ds k).card : ℝ)*Z^(2*F+2*(D+E)) := by
        simpa only [Finset.sum_const,nsmul_eq_mul] using
          Finset.sum_le_sum (fun L _ => hterm k hk L)
      _ ≤ Z^C*Z^(2*F+2*(D+E)) := mul_le_mul_of_nonneg_right (hprojectors k hk) (by positivity)
      _ = _ := (Real.rpow_add hZ _ _).symm
  unfold secondProjectedAbsoluteEnvelope
  calc
    _ ≤ scale*((labels.card : ℝ)*Z^(C+(2*F+2*(D+E)))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hinner
    _ ≤ Z^A*(Z^B*Z^(C+(2*F+2*(D+E)))) :=
      mul_le_mul hscale' (mul_le_mul_of_nonneg_right hlabels (by positivity))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ,← Real.rpow_add hZ]; congr 1; ring

theorem second_projected_values_le_retained {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (t : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (weight : α → ℂ)
    (scale θ u v : ℝ) (hscale : 0 ≤ scale) (hw : ∀ k ∈ labels, ‖weight k‖ ≤ 1) :
    secondProjectedJointValues labels s Ds t n z weight scale θ u v ≤
      secondProjectedJointRetained labels s Ds t n z scale θ u v := by
  unfold secondProjectedJointValues secondProjectedJointRetained
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro L hL
  by_cases hm : (UniqueFactorizationMonoid.moebius L : ℂ) = 0
  · simp [hm]
  have hpair := ((s k).withProjector L).values_le_retainedPair
    (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hm)
    (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
    (dyadicScale (n k 2)) (dyadicScale (n k 3))
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hscale]
  calc
    _ = (scale*‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*‖weight k‖)*
      (‖((s k).withProjector L).toKernelLabel.leftValue
        (t k+2*Real.pi*(u-θ)) (z k) (dyadicScale (n k 2))‖ *
       ‖((s k).withProjector L).toKernelLabel.rightValue
        (t k+2*Real.pi*(v-(-θ))) (z k) (dyadicScale (n k 3))‖) := by ring
    _ ≤ (scale*‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*1)*
      ((s k).withProjector L).retainedPair
        (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
        (dyadicScale (n k 2)) (dyadicScale (n k 3)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hw k hk) (by positivity)) hpair
        (by positivity) (by positivity)
    _ = _ := by ring

theorem second_projected_values_le_absolute {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (t : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (weight : α → ℂ)
    (scale θ u v : ℝ) (hscale : 0 ≤ scale) (hw : ∀ k ∈ labels, ‖weight k‖ ≤ 1) :
    secondProjectedJointValues labels s Ds t n z weight scale θ u v ≤
      secondProjectedAbsoluteEnvelope labels s Ds n scale := by
  unfold secondProjectedJointValues secondProjectedAbsoluteEnvelope
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro L hL
  have hp := (((s k).withProjector L).toKernelLabel).values_le_absoluteEnvelope
    (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
    (dyadicScale (n k 2)) (dyadicScale (n k 3))
  have he : (((s k).withProjector L).toKernelLabel).absoluteEnvelope
      (dyadicScale (n k 2)) (dyadicScale (n k 3)) =
      (s k).toKernelLabel.absoluteEnvelope (dyadicScale (n k 2)) (dyadicScale (n k 3)) := rfl
  rw [he] at hp
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hscale]
  calc
    _ = (scale*‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*‖weight k‖)*
      (‖((s k).withProjector L).toKernelLabel.leftValue
        (t k+2*Real.pi*(u-θ)) (z k) (dyadicScale (n k 2))‖ *
       ‖((s k).withProjector L).toKernelLabel.rightValue
        (t k+2*Real.pi*(v-(-θ))) (z k) (dyadicScale (n k 3))‖) := by ring
    _ ≤ (scale*‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*1)*
      (s k).toKernelLabel.absoluteEnvelope (dyadicScale (n k 2)) (dyadicScale (n k 3)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hw k hk) (by positivity)) hp
        (by positivity) (by positivity)
    _ = _ := by ring

/-- The coarse input is a finite sum of original absolute coefficients,
with exact dyadic denominators; it contains no allocated product estimate. -/
theorem joint_second_kernel_from_local_retained_absolute
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν B target : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι]
        (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
        (t K R : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (weight : α → ℂ),
      (∀ k ∈ labels, ‖weight k‖ ≤ 1) → ∀ Z scale Ch Ct : ℝ,
      1 ≤ Z → 0 ≤ scale → 0 ≤ Ch → 0 ≤ Ct →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        secondProjectedJointRetained labels s Ds t n z scale θ u v ≤ Ch*Z^target) →
      secondProjectedAbsoluteEnvelope labels s Ds n scale ≤ Ct*Z^B →
      (∑ k ∈ labels, ∑ L ∈ Ds k,
        ‖(((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius L : ℂ)*((scale : ℂ)*weight k)) *
            ((s k).withProjector L).toKernelLabel.kernelRow
              (t k) (z k) W (K k) (R k) (n k)‖) ≤ C*((Ch+Ct)*Z^target) := by
  obtain ⟨N,hpoly⟩ := three_variable_polynomial_extension ν B target hν
  obtain ⟨C,hC,hkernel⟩ := joint_second_kernel_norm_sum_from_values W decay N N N
  refine ⟨N,C,hC,?_⟩
  intro ι α instι instDι labels s Ds t K R n z weight hweight Z scale Ch Ct hZ hscale hCh hCt hlocal habsolute
  have hglobal := hpoly Z Ch Ct hZ hCh hCt
    (secondProjectedJointValues labels s Ds t n z weight scale)
    (fun θ u v hθ hu hv => (second_projected_values_le_retained labels s Ds t n z weight
      scale θ u v hscale hweight).trans (hlocal θ u v hθ hu hv))
    (fun θ u v => (second_projected_values_le_absolute labels s Ds t n z weight
      scale θ u v hscale hweight).trans habsolute)
  have hh := hkernel (labels.sigma Ds) (fun q => ((s q.1).withProjector q.2).toKernelLabel)
    (fun q => t q.1) (fun q => K q.1) (fun q => R q.1) (fun q => n q.1) (fun q => z q.1)
    (fun q => (UniqueFactorizationMonoid.moebius q.2 : ℂ)*((scale : ℂ)*weight q.1))
    ((Ch+Ct)*Z^target) (by
      intro θ u v
      simpa only [Finset.sum_sigma,secondProjectedJointValues] using hglobal θ u v)
  simpa only [Finset.sum_sigma] using hh

theorem joint_second_kernel_from_local_retained_absolute_uniform
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ target : ℝ, lower ≤ target →
      ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι]
        (labels : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
        (t K R : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (weight : α → ℂ),
      (∀ k ∈ labels, ‖weight k‖ ≤ 1) → ∀ Z scale Ch Ct : ℝ,
      1 ≤ Z → 0 ≤ scale → 0 ≤ Ch → 0 ≤ Ct →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        secondProjectedJointRetained labels s Ds t n z scale θ u v ≤ Ch*Z^target) →
      secondProjectedAbsoluteEnvelope labels s Ds n scale ≤ Ct*Z^B →
      (∑ k ∈ labels, ∑ L ∈ Ds k,
        ‖(((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius L : ℂ)*((scale : ℂ)*weight k)) *
            ((s k).withProjector L).toKernelLabel.kernelRow
              (t k) (z k) W (K k) (R k) (n k)‖) ≤ C*((Ch+Ct)*Z^target) := by
  obtain ⟨N,hpoly⟩ := three_variable_polynomial_extension_lower ν B lower hν
  obtain ⟨C,hC,hkernel⟩ := joint_second_kernel_norm_sum_from_values W decay N N N
  refine ⟨N,C,hC,?_⟩
  intro target htarget ι α instι instDι labels s Ds t K R n z weight hweight Z scale Ch Ct hZ hscale hCh hCt hlocal habsolute
  have hglobal := hpoly target htarget Z Ch Ct hZ hCh hCt
    (secondProjectedJointValues labels s Ds t n z weight scale)
    (fun θ u v hθ hu hv => (second_projected_values_le_retained labels s Ds t n z weight
      scale θ u v hscale hweight).trans (hlocal θ u v hθ hu hv))
    (fun θ u v => (second_projected_values_le_absolute labels s Ds t n z weight
      scale θ u v hscale hweight).trans habsolute)
  have hh := hkernel (labels.sigma Ds) (fun q => ((s q.1).withProjector q.2).toKernelLabel)
    (fun q => t q.1) (fun q => K q.1) (fun q => R q.1) (fun q => n q.1) (fun q => z q.1)
    (fun q => (UniqueFactorizationMonoid.moebius q.2 : ℂ)*((scale : ℂ)*weight q.1))
    ((Ch+Ct)*Z^target) (by
      intro θ u v
      simpa only [Finset.sum_sigma,secondProjectedJointValues] using hglobal θ u v)
  simpa only [Finset.sum_sigma] using hh

#print axioms second_projected_values_le_absolute
#print axioms joint_second_kernel_from_local_retained_absolute
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondAbsoluteCutoff -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceAbsoluteMass ; sha256 47c25a7899686a1f1f900a836899f5a294db9b6e8bc6aa4d0412d483f597f811 -/
section



/-! The literal Input coefficient mass controls Fourier tails uniformly
in all characters, shifts, masks and common ideals. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSourceProfileMassUniform
open CenteredMomentActiveSource CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O

 theorem residual_absolute_mass_le_all (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C : Ideal O) (hC : C ≠ 0) :
    (∑ I ∈ residualPool C hC S, ‖β (C*I)‖) ≤ sourceAbsoluteMass S β := by
  have hsub : (residualPool C hC S).image (fun I => C*I) ⊆ S := by
    intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact (mem_residualPool C hC S I).mp hI
  calc
    _ = ∑ I ∈ (residualPool C hC S).image (fun I => C*I), ‖β I‖ := by
      rw [Finset.sum_image]
      intro I hI J hJ he
      exact mul_left_cancel₀ hC he
    _ ≤ sourceAbsoluteMass S β :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ => norm_nonneg _)

 theorem sourceAbsoluteMass_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    sourceAbsoluteMass (activeSource S β) β = sourceAbsoluteMass S β := by
  unfold sourceAbsoluteMass activeSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : β I = 0 <;> simp [h]

 theorem common_second_absolute_mass {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C L : Ideal O) (hC : Supported C) :
    sourceAbsoluteMass (activeSource (commonSecondColumns s C hC) (commonSecondBeta s C L))
      (commonSecondBeta s C L) ≤ sourceAbsoluteMass s.columns s.beta := by
  rw [sourceAbsoluteMass_active]
  apply le_trans _ (residual_absolute_mass_le_all s.columns s.beta C hC.1)
  unfold sourceAbsoluteMass commonSecondColumns commonSecondBeta
  apply Finset.sum_le_sum
  intro I hI
  split_ifs <;> simp

 def originalAbsoluteProfile {ι : Type*} [Fintype ι] (s : Input ι) (B₁ B₂ : ℝ) : ℝ :=
  2*128^(Fintype.card ι+2)*(∏ j,s.M j)*B₁*B₂*
    (max 1 s.upper)^Fintype.card ι*max 1 s.b₁*max 1 s.b₂

 theorem original_absolute_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hb₁ : ∀ x, ‖s.W₁ x‖ ≤ B₁) (hb₂ : ∀ x, ‖s.W₂ x‖ ≤ B₂) :
    sourceAbsoluteMass (original s R seed).columns (original s R seed).beta ≤
      originalAbsoluteProfile s B₁ B₂*CenteredMomentExceptionalAmplitudePair.volume s.toData := by
  letI : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
  have hz (i) : s.W i 0 = 0 := by
    by_contra hn
    exact (not_le_of_gt s.lower_pos) ((s.slot_support i) hn).1
  have hm := profile_mass_explicit s.W s.W₁ s.W₂ (fun _ => max 1 s.upper) s.M
    (max 1 s.b₁) (max 1 s.b₂) B₁ B₂ (fun _ => by positivity) (by positivity) (by positivity)
    (fun j => zero_le_one.trans (s.M_ge_one j)) hB₁ hB₂ hz hz₁ hz₂
    (fun j x hx => ((s.slot_support j) hx).2.trans (le_max_right _ _))
    (fun x hx => (s.support₁ hx).trans (le_max_right _ _))
    (fun x hx => (s.support₂ hx).trans (le_max_right _ _))
    s.W_bound hb₁ hb₂ R s.ν s.ν_bound s.P s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)
    1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (Fintype.piFinset s.pools)
  have hc := finiteColumnCoefficient_mass (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  dsimp only [sourceAbsoluteMass,OriginalData.columns,OriginalData.beta,OriginalData.profile,original]
  apply hc.trans (hm.trans_eq ?_)
  simp only [map_one,Nat.cast_one,one_mul,div_one,Finset.prod_const,Finset.card_univ,
    originalAbsoluteProfile,CenteredMomentExceptionalAmplitudePair.volume]
  ring

 theorem actual_common_absolute_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : CommonSecondKernelLabel ι) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hz₁ : s.input.W₁ 0 = 0) (hz₂ : s.input.W₂ 0 = 0)
    (hb₁ : ∀ x, ‖s.input.W₁ x‖ ≤ B₁) (hb₂ : ∀ x, ‖s.input.W₂ x‖ ≤ B₂) :
    sourceAbsoluteMass s.toKernelLabel.columns s.toKernelLabel.beta ≤
      originalAbsoluteProfile s.input B₁ B₂*CenteredMomentExceptionalAmplitudePair.volume s.input.toData :=
  (common_second_absolute_mass (original s.input s.puncture s.seed)
    s.firstCommon s.firstProjector s.hfirst).trans
    (original_absolute_mass s.input s.puncture s.seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂)

#print axioms original_absolute_mass
#print axioms actual_common_absolute_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceAbsoluteMass -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourcePhysicalBins ; sha256 119cd728ee4724b50e8e324b8533a23e6b08b45a577b4abec0e00d08566af4b3 -/
section



/-! The actual source ray coefficients and projector pool are retained in
physical bin contributions. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFixedRay CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondSectorColumns CenteredMomentMobiusRegroup
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]

namespace CommonSecondKernelLabel

def withRays (s : CommonSecondKernelLabel Slot) (χ ξ : RayCharacter) : CommonSecondKernelLabel Slot :=
  {s with leftRay := χ, rightRay := ξ}

def physicalRayWeight (s : CommonSecondKernelLabel Slot) : ℂ :=
  pairCoeff (phaseTable (primaryGenerator s.second.val.1) (primaryGenerator s.second.val.2))
    s.leftRay s.rightRay

theorem physicalRayWeight_norm (s : CommonSecondKernelLabel Slot) : ‖s.physicalRayWeight‖ ≤ 1 :=
  pairCoeff_norm_le _ 1 (fun u v => phaseTable_norm _ _ u v) _ _

def physicalProjectors (s : CommonSecondKernelLabel Slot) : Finset (Ideal O) :=
  divisorPool Finset.univ (fun J : sectorPool s.second.val.2 s.toKernelLabel.hD.1
    s.toKernelLabel.columns => (J : Ideal O))

def physicalRowTerm (s : CommonSecondKernelLabel Slot) (H P : ℝ)
    (t : ℝ) (z : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (n : Fin 4 → ℤ) (D : Ideal O) : ℂ :=
  (secondPrecountFactor H P s.second.val.1 s.second.val.2 s.partition K n : ℂ)*
    (UniqueFactorizationMonoid.moebius D : ℂ)*s.physicalRayWeight*
    (s.withProjector D).toKernelLabel.kernelRow t z W K R n

theorem physicalRowTerm_eq_high (s : CommonSecondKernelLabel Slot) (Z A c P : ℝ)
    (t : ℝ) (z : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (n : Fin 4 → ℤ) (D : Ideal O) :
    s.physicalRowTerm (Z^(A-c)) P t z W K R n D =
      ((UniqueFactorizationMonoid.moebius D : ℂ)*(s.actualPrecount Z A c P K n : ℂ)*
        s.physicalRayWeight)*(s.withProjector D).toKernelLabel.kernelRow t z W K R n := by
  simp only [physicalRowTerm,actualPrecount]
  ring

/-- The source's literal physical block, with binning after the transform.
Every projector and both fixed ray characters remain inside this expression. -/
theorem physicalBlock_bin_majorant {κ : Type*} [Fintype κ]
    (s : CommonSecondKernelLabel Slot) (t R : ℝ) (rows : Finset O) (bin : O → κ)
    (hrows : ∀ z ∈ rows, z ≠ 0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (n : Fin 4 → ℤ) (H P : ℝ) (hH : 0 < H) (hP : 0 < P) :
    ‖physicalBlock s.parent t s.toKernelLabel.columns s.toKernelLabel.beta
      s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD s.partition R rows W K n‖/
      (H*P) ≤
      ∑ b : κ, ∑ D ∈ s.physicalProjectors, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ∑ z ∈ rows.filter (fun z => bin z = b),
          ‖(s.withRays χ ξ).physicalRowTerm H P t z W K R n D‖ := by
  exact actual_physicalBlock_bin_majorant s.parent t s.toKernelLabel.columns s.toKernelLabel.beta
    s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD s.toKernelLabel.hCD
    s.partition R rows bin hrows W K hK n H P hH hP

end CommonSecondKernelLabel
#print axioms CommonSecondKernelLabel.physicalRayWeight_norm
#print axioms CommonSecondKernelLabel.physicalBlock_bin_majorant
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourcePhysicalBins -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.ActiveFourth ; sha256 83b79d385760df0d4dad486c4db5ca2af36041d3d04cc09597a578a51cb022ae -/
section




/-! Actual rowwise coefficient choices on one finite dilation box. Inactive
choices are replaced by a positive admissible scale before invoking the moment
bound, and their nonnegative contribution is subsequently discarded. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Cycle25.Numerator
open Cycle25.Weighted.Numerator Cycle25.Weighted.Numerator.PhysicalMoment
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

def fallbackCoefficientScale (b Y C Cu U m:ℝ) : ℝ := min (b*Y) (C*U^m*Y/Cu)

lemma fallback_scale_admissible (b Y C Cu U m:ℝ)
    (hb:0 < b) (hY:0 < Y) (hC:0 < C) (hCu:0 < Cu) (hU:0 < U) :
    0 < fallbackCoefficientScale b Y C Cu U m ∧
      fallbackCoefficientScale b Y C Cu U m ≤ b*Y ∧
      Cu ≤ C*U^m*(Y/fallbackCoefficientScale b Y C Cu U m) := by
  have hp : 0 < fallbackCoefficientScale b Y C Cu U m := by
    unfold fallbackCoefficientScale
    exact lt_min (mul_pos hb hY) (by positivity)
  refine ⟨hp,min_le_left _ _,?_⟩
  rw [←mul_div_assoc,le_div_iff₀ hp]
  have hh := (le_div_iff₀ hCu).mp (min_le_right (b*Y) (C*U^m*Y/Cu))
  simpa only [fallbackCoefficientScale,mul_comm Cu] using hh

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem certified_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap:ℝ) (hkaplo:7/10≤ kap) (hkaphi:kap≤3/4)
    (hkapbeta:2*HeckeZeroSupremum.beta-1≤ kap) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,(1/2:ℝ) ≤ d → d ≤ Cycle25.h+Cycle25.rowExtension →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ selectedCapacity kap ((2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap))
        ((j:ℝ)*boxWidth+boxWidth) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(Cycle25.ly/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := certified_original_numerator_fourth F kap hkaplo hkaphi hbeta hkapbeta G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_physical_cutoff_le_base b hb.le] with U hmom hcutoff
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN d hd hdmax j hj T width z height hw hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(Cycle25.ly/d)
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
  let m := 1-Cycle25.ly/d+(j:ℝ)*boxWidth+boxWidth
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hNu (i:rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i:rows) : Lc i ≤ 1 := by
    apply (div_le_one (mul_pos hCcond (hNu i))).mpr
    exact (data i).combined_le_row
  have hcut : b*Y ≤ U^((coefficientBoxCount boxWidth:ℝ)*boxWidth) := by
    apply (hcutoff.2 d hd).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le
      (coefficientBoxCount_extent boxWidth hbox).1
  have hcombinedActive (i:rows) (hi:active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).2
    rw [hi.2] at hspec
    have hb' : max 1 ((data i).combinedConductor*N i/(Ccond*rowNorm i.val)) ≤
        U^((j:ℝ)*boxWidth+boxWidth) := by
      have hprod : Lc i*N i = (data i).combinedConductor*N i/(Ccond*rowNorm i.val) := by
        dsimp only [Lc]
        ring
      have hexp : ((j:ℝ)+1)*boxWidth = (j:ℝ)*boxWidth+boxWidth := by ring
      rw [hprod,hexp] at hspec
      exact hspec
    have hc := combined_scale_of_dilation (data i).combinedConductor Ccond (rowNorm i.val)
      (N i) Y U (Cycle25.ly/d) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hb'
    simpa only [m,add_assoc] using hc
  let Nsafe (i:rows) := if active i then N i
    else fallbackCoefficientScale b Y Ccond (data i).combinedConductor U m
  have hsafe (i:rows) : 0 < Nsafe i ∧ Nsafe i ≤ b*Y ∧
      (data i).combinedConductor ≤ Ccond*U^m*(Y/Nsafe i) := by
    dsimp only [Nsafe]
    split_ifs with hi
    · exact ⟨hN i,hi.1,hcombinedActive i hi⟩
    · exact fallback_scale_admissible b Y Ccond (data i).combinedConductor U m
        hb hY hCcond (data i).combined_pos hUp
  obtain ⟨hm,hmmax⟩ := physical_coefficient_box_geometry d boxWidth annulusSlack
    hd hdmax hbox hann.le hsmall j hj
  have hcapacity := physical_reflected_capacity_or_empty_subtype T width kap (Cycle25.ly/d)
    ((j:ℝ)*boxWidth) boxWidth annulusSlack (by linarith) hw hselected
  have hQ' (i:rows) : ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
      (U^(width s)) (z s)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m hY (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax (fun i=>(hsafe i).2.2) T width z height (fun i=>(hw i).le) hwmax hz hh him
    (by simpa only [m] using hcapacity) hQ'
  apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi:active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num:4≠0),zero_mul]
    positivity

end Cycle25.Numerator
end

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.ActiveFourth -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowSelectedBound ; sha256 0963a05f933f1c086e8aa3e788169a33029d3ac2b68d9295edc14b5dd4fe2e84 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSelectedBound.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma gaussianFixedWindow_support : Function.support gaussianFixedWindow⊆Set.Icc (1/2:ℝ) 2 := by
  intro y hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))

lemma lowReflectionMask_bad_ideals (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {lowReflectionMask η S hS}*(1:Id) := by
  intro P hP
  rw [mul_one,lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,calibrationForSet_span]
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun P : Id=> P) (hbad hP)) _

theorem low_selected_physical_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0< Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0< C ∧ 1< Z₀ ∧
    ∀(Z d ell0 shift : ℝ),Z₀≤ Z→0≤ d→d≤ Submission20261012.Global.ell→0≤ ell0→ell0≤ Submission20261012.Global.ell-d+ε→|shift|≤ε→
    ∀(R : Finset O),(∀z∈R,z≠0 ∧ elementNorm z≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d))→
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (∀i,1≤ H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤ H i)→(∏i,H i)≤ Z^ell0→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) (Z^(1+ell0+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := LowReflection.low_original_completed_energy
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0< C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=> hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=> Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=> hdis (fun h=> hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤ K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial L
        (fun i I=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+507*ε) := by
    convert he Z d ell0 shift hZ hd hd1 hell hellcap hshift (lowIdealRows R) hparents hcard L H
      hlists (fun i=> lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=> lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=> lowPrimeIdealList_norm _ _ (fun P hP=> hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=> low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Oˣ))=> hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤ Z^(((1-Submission20261012.Global.ell)-d)+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^(((1-Submission20261012.Global.ell)-d)+507*ε) := by ring
    _≤_ := by gcongr <;> linarith

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowSelectedBound -/
