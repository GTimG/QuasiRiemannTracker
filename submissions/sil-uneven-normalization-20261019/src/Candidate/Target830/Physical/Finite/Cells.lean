import Candidate.Target830.Physical.Transport.PrincipalRemainderRegion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Candidate.Target830.Physical.Low.Detector.GaussianSum
import Candidate.Target830.Physical.LowGeometry
import Candidate.Target830.Physical.Transport.LowNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowWindowBound
import Candidate.Target830.Physical.Transport.ProbeDefinition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Physical
import Candidate.Target830.Physical.BaselineMoments
import Candidate.Target830.Physical.Transport.PrincipalSignal
import Candidate.Cycle25.Assembly.Continuation
import Candidate.Target830.Physical.FinalHeight
import Candidate.Target830.Physical.Chosen
import Candidate.Target830.Physical.Transport.HighApproximation
import Candidate.Target830.Physical.Finite.Partition

/- Original module: Candidate.Target830.Physical.Transport.SourceCorrection. -/
section

set_option autoImplicit false
namespace Target830Physical.Transport
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.PrincipalSignalComparison
open OAI.SevenEighths.HeckeFamily OAI.SevenEighths.ProbePhysical

/-- The original source correction, analytically extended to the fresh boundary.
This proves the analytic clause and carries no source-moment or probe premise. -/
theorem actual_source_analytic
    (S : Finset (Ideal OAI.SevenEighths.HeckeFamily.O)) (hS : SourceExclusions S)
    (η : Character) :
    (∀ I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|Arithmetic.theta< s.re} ∧
    (∀s : ℂ,Arithmetic.theta< s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  refine ⟨excludePrimes_mask η S hS.prime,?_,?_⟩
  · exact remainder_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6)
      (by norm_num) (by norm_num)
  · intro s hs
    exact remainder_globalClosedCorrection_bound η S hS.tail s 1 (1/6)
      hs.le (by norm_num) (by norm_num)

end
end Target830Physical.Transport
#print axioms Target830Physical.Transport.actual_source_analytic
end

/- Original module: Candidate.Target830.Physical.Low.Detector.Normalized. -/
section
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Detector/LowWindowBound, Detector/LowNormalized.
Apache-2.0 upstream attribution retained. Actual probe scales and total ray length use Cycle63. -/
namespace OAI
noncomputable section
namespace SevenEighths.Target830PhysicalProbeLow
section
open scoped Classical ContDiff
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma compensatedPhysicalProbe_window_scale {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) (c : ℂ) :
    compensatedPhysicalProbe η C W0 W1 slots (fun i x=> c*W i x) Yp X Y Z=
      c^K*compensatedPhysicalProbe η C W0 W1 slots W Yp X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc]
  exact (Finset.mul_sum ..).symm
theorem original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤ Target830Physical.Arithmetic.ell) (R : Set Id)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤ B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(Target830Physical.Arithmetic.x:ℝ)) (Z^(Target830Physical.Arithmetic.y:ℝ)) Z‖≤ C*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+loss) := by
  let D := max 1 B
  have hD : 0< D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=> W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0< ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤ loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=> Z^(ell i))
    (Z^(Target830Physical.Arithmetic.x:ℝ)) (Z^(Target830Physical.Arithmetic.y:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤ D^K*(C*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤ D^K*(C*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+loss)) := by gcongr
    _=_ := by ring
end
section
open scoped Classical ContDiff
open Filter
open ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
theorem original_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=Target830Physical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Target830Physical.Arithmetic.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(Target830Physical.Arithmetic.x:ℝ)) (Z^(Target830Physical.Arithmetic.y:ℝ)) Z/normer‖≤
        C*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1< max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := Target830PhysicalLowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring
end
end SevenEighths.Target830PhysicalProbeLow
end
end OAI

#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.compensatedPhysicalProbe_window_scale
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.original_ray_compensatedPhysicalProbe_low_loss
#print axioms OAI.SevenEighths.Target830PhysicalProbeLow.original_normalized_compensatedPhysicalProbe_low
end

/- Original module: Candidate.Target830.Physical.Low.Probe. -/
section
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/

set_option autoImplicit false

/-! The canonical compensated physical probe at the actual Cycle63 lengths.
Adapted from weighted upstream 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace OAI
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.Target830PhysicalLow
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=Target830Physical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=> Z^((Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := Target830PhysicalProbeLow.original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=> h.2)⟩

end SevenEighths.Target830PhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.Target830PhysicalLow.normalizedProbe_low
end

/- Original module: Candidate.Target830.Physical.FinalSourceProbe. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FinalAssembly
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical OAI.SevenEighths.Target830.Physical PrincipalSignalComparison
open OAI.SevenEighths.Target830.Physical.Assembly

def sourceProbe (D : BaselineData) (F : BaselineSourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  Target830PhysicalLow.normalizedProbe F.modulus ⊤ F.S F.maximal D.length 1 2
    (fun _=> F.w) F.W F.W η

theorem sourceProbe_low (D : BaselineData) (F : BaselineSourceData D)
    (loss : ℝ) (hloss : 0< loss) (η : Character) :
    sourceProbe D F η=O[atTop](fun Z : ℝ=> Z^(Assembly.signal theta+loss)) := by
  have hh := Target830PhysicalLow.normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss D.length D.slots_pos
    D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  exact hh

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|theta< s.re} ∧
    (∀s : ℂ,theta< s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact Target830Physical.Transport.actual_source_analytic S hS η

theorem fixed_source_contract (D : BaselineData) (F : BaselineSourceData D)
    (loss sigma : ℝ) (hloss : 0< loss)
    (herror : ∀η : Character,
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Assembly.signalShift-sigma))) :
    Cycle25.PrimitiveProbeContract theta Assembly.signalShift loss sigma := by
  intro η _
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  simpa only [Assembly.signal] using sourceProbe_low D F loss hloss η
end
end OAI.SevenEighths.Target830.Physical.FinalAssembly

#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.sourceProbe_low
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.actual_source_analytic
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.fixed_source_contract
end

/- Original module: Candidate.Target830.Physical.FinalFixedHigh. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                         
                                    
                                      
                                                   

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FinalAssembly
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics OAI.SevenEighths
open OAI.SevenEighths.Target830.Physical.Assembly
open HeckeFamily ProbePhysical OAI.SevenEighths.Target830.Physical PrincipalSignalComparison Target830PhysicalHighTransport

/-- The finite numerator remains the honest analytic integration prerequisite. -/
def FixedFiniteNumeratorInput (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) : Prop :=
  ∀n : ℕ,0< n → ∀η : Character,
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=> F.w) F.W F.W n η

/-- The finite numerator bound for one character. -/
def FixedFiniteNumeratorInputAt (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (η : Character) : Prop :=
  ∀n : ℕ,0< n →
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=> F.w) F.W F.W n η

theorem sourceProbe_high_of_finite_numerator (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : theta≤ HeckeZeroSupremum.beta)
    (hfinite : FixedFiniteNumeratorInput D F P τ) :
    ∀η : Character,
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)< Assembly.signal theta := by
      norm_num [Assembly.signal,Assembly.signalShift,theta,x,ell,h]
    linarith
  have hcap : h+rowPadding≤(7/8:ℝ)-1/100 := by
    norm_num [h,rowPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [rowPadding,Target830Physical.Transport.rowExtension]) P.floor_budget hfinite
  simpa only [sourceProbe,Target830Physical.Assembly.signalShift,Assembly.signalShift,Target830Physical.Arithmetic.x,Target830Physical.Arithmetic.ell] using hh
theorem sourceProbe_high_of_finite_numerator_at (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : theta≤ HeckeZeroSupremum.beta)
    (η : Character) (hfinite : FixedFiniteNumeratorInputAt D F P τ η) :
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)< Assembly.signal theta := by
      norm_num [Assembly.signal,Assembly.signalShift,theta,x,ell,h]
    linarith
  have hcap : h+rowPadding≤(7/8:ℝ)-1/100 := by
    norm_num [h,rowPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator_at F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [rowPadding,Target830Physical.Transport.rowExtension]) P.floor_budget η hfinite
  simpa only [sourceProbe,Target830Physical.Assembly.signalShift,Assembly.signalShift,Target830Physical.Arithmetic.x,Target830Physical.Arithmetic.ell] using hh
end
end OAI.SevenEighths.Target830.Physical.FinalAssembly


#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.sourceProbe_high_of_finite_numerator
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.sourceProbe_high_of_finite_numerator_at
end

/- Original module: Candidate.Target830.Physical.Finite.Cells. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open OAI.SevenEighths.Target830.Physical FinalAssembly Target830PhysicalHighTransport
open OAI.SevenEighths.Target830.Physical.Assembly
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

instance fixedProduct (D : BaselineData) (F : BaselineSourceData D) : NeZero (∏P∈F.S,P) :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

def primePool (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (j : Fin D.N) :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j))

theorem poolOutside (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) :
    ∀j P,P∈primePool D F Z j→P.val∉F.S :=
  fun j P hP=>(mem_pool _ F.S 1 2 (Z^(D.length j)) P).mp hP |>.2.2.2

def normalizer (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) : ℂ :=
  actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=> F.w) F.W F.W Z

def fullW (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (R : Finset FreeRow) (a H : FreeRow→ℝ) : ℂ :=
  Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η R
    (primePool D F Z) (poolOutside D F Z) (fun _ y=>(F.w y:ℂ)) (fun j=> Z^(D.length j))
    F.W F.W (Z^OAI.SevenEighths.Target830.x) (Z^OAI.SevenEighths.Target830.y) Z D.e a H

def selectedRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (grid : FreeRow→ℕ) :=
  supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(OAI.SevenEighths.Target830.h+rowPadding))) grid

def cellRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (idx grid : FreeRow→ℕ) (k i j : ℕ) :=
  cubeBinRows (selectedRows D F Z grid∩dyadicRows 1 k) idx grid i j

def cellTarget : ℝ :=
  HeckeZeroSupremum.beta+Assembly.signalShift-Scalar.sourceReserve-
    (HeckeZeroSupremum.beta-OAI.SevenEighths.Target830.theta)/2

structure CellFacts (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z τ : ℝ) (R : Finset FreeRow) (d a : ℝ) (i : ℕ) : Prop where
  d_lower : (1/200:ℝ)≤ d
  d_upper : d≤ OAI.SevenEighths.Target830.dPlus
  a_lower : (51/100:ℝ)< a
  a_upper : a≤7/8
  source_rows : ∀u∈R,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-D.t)
  moment_rows : ∀u∈R,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^d
  frequency_lower : ∀u∈R,Z^(d-2*D.t)≤ rowNorm u
  natural_nonprincipal : ∀u∈R,∀θ,(rayCubeFamily F.modulus ⊤ le_top u θ).residue≠1
  next_maximum : ∀u∈R,detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    (3*(i+1:ℕ)*Z^τ)< a+2*D.e
  current_maximum : ∀u∈R,a≤ detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    ((3*i:ℕ)*Z^τ)

theorem selected_rows_facts (D : BaselineData) (F : BaselineSourceData D)
    (Z : ℝ) (grid : FreeRow→ℕ) :
    ∀u∈selectedRows D F Z grid,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤ Z^(OAI.SevenEighths.Target830.h+rowPadding) := by
  intro u hu
  rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hb,hcal,_⟩
  rcases mem_rowBand.mp hb with ⟨hne,hlo,hhi⟩
  exact ⟨hne,hlo,hcal,hhi.le⟩
end
end OAI.SevenEighths.Target830.Physical.FiniteNumerator

#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.poolOutside
#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.selected_rows_facts
end
