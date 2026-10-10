import ZetaZeroFree.Analytic.Probe.Collected
import ZetaZeroFree.Analytic.SourceData
import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalPartition
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins

namespace ZetaZeroFree.Analytic.Probe
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss ProbeHighRowFamily
local notation "O" => HeckeFamily.O
theorem source_small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/200:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50))
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_source_physical_dyad_bound K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hdyads⟩ := bounded_dyadic_power_sum 1 (by norm_num)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hcard : (F.card:ℝ)≤D*Z^(1/200:ℝ) := by
    calc
      _ = ∑_n∈F,(1:ℝ) := by simp
      _ ≤ ∑n∈F,((2:ℝ)^n)^(1:ℝ) := Finset.sum_le_sum (fun n _=>by simpa using one_le_pow₀ (by norm_num : (1:ℝ)≤2))
      _ ≤ D*(Z^(1/200:ℝ))^(1:ℝ) := hdyads _ (by positivity) F hF
      _ = _ := by rw [Real.rpow_one]
  have hb (n : ℕ) (hn : n∈F) := hmain η Z ((2:ℝ)^n) hZ (one_le_pow₀ (by norm_num)) (hF n hn)
    (R n) (hR n hn) T hT hdis length hl0 hl W hWS hWB
  calc
    _ ≤ ∑_n∈F,C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/20+8*e) := Finset.sum_le_sum hb
    _ = (F.card:ℝ)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/20+8*e)) := by simp
    _ ≤ (D*Z^(1/200:ℝ))*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/20+8*e)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C*D*(η.modulus.absNorm:ℝ)^δ*Z^((1/200:ℝ)+(HeckeZeroSupremum.beta-67/99-1/20+8*e)) := by
      rw [Real.rpow_add hZ0 (1/200:ℝ) (HeckeZeroSupremum.beta-67/99-1/20+8*e)];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

theorem source_small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/200:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e) := by
  obtain ⟨C,hC,hmain⟩ := source_small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖≤N*g n := norm_finitePhysicalRows_le_absolute
    e (HeckeZeroSupremum.beta+8*e) (1/2) (17/50) he he' (by linarith) le_rfl
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

theorem source_canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/200:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e) := by
  obtain ⟨C,hC,hmain⟩ := source_small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/200:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem source_canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((25/33:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((25/33:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨C,hC,hmain⟩ := source_large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((25/33:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

theorem source_canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+Z^(-saving)) := by
  obtain ⟨Cs,hCs,hs⟩ := source_canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := source_canonical_large_original_tail K δ a b B ζ saving hδ (by linarith) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
    (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/200:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/200:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/200:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/200:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

theorem source_canonical_probe_minus_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+Z^(-saving)) := by
  obtain ⟨C0,hC0,h0⟩ := source_canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((25/33:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+Z^(-saving)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤E := by dsimp [E];have : 0≤Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

theorem source_canonical_probe_exists_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀(η : Character) (Z : ℝ),1≤Z → 2<Z^τ →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀ψ : FreeRow→ι→Character,∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (ψ u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (ψ u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,hbound⟩ := source_canonical_probe_minus_cube (ι:=ι) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha hb hB hβ S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  intro η Z hZ hZT T hT hdis length hl0 hl hpool W hWS hWB ψ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he hZT n hn hwidth S hS.prime η ψ
  refine ⟨idx,grid,?_,?_,?_⟩
  · intro u
    exact ⟨(hbins u).1,(hbins u).2.1,(hbins u).2.2.1,(hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    exact ⟨ha0,ha1,hlo,hhi,hnext,hzero⟩
  · apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
      (fun u=>51/100+e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx ψ
    intro u hu
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    refine ⟨ha0,ha1,hZT,hBH,?_,hnext⟩
    have : 0≤Z^τ := Real.rpow_nonneg (by linarith) _
    linarith

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
theorem source_canonical_probe_exists_ray_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,n,hn,hchoice⟩ := source_canonical_probe_exists_cube (ι:=RayQuotient.Characters M H)
    K e δ a b B ζ saving τ he he' hδ hδ' hζ hζ' hτ ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ,
    ProbeRayCharacterFamily.large_supported_twists_eventually M (1/200) (by norm_num)]
    with Z hZ hlarge
  intro η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨idx,grid,hlabel,hbins,herror⟩ := hchoice η Z hZ.1 hZ.2 T hT hdis length hl0 hl hpool W hWS hWB
    (rayCubeFamily M H hH)
  refine ⟨idx,grid,hlabel,hbins,?_,herror⟩
  intro u hu hcal
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hcal
  have hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1 :=
    hlarge u (mem_rowBand.mp hu).2.1 hs H hH
  refine ⟨hnp,?_,?_⟩
  · exact ProbeRayCharacterFamily.raw_twisted_conductor M H hH u
  · intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates S hS.prime η u
      (rayCubeFamily M H hH u) hnp' _).trans_lt (hbins u).2.2.2.2.1

open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual

theorem source_actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=5/33)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (5/33)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=>Z^(ell j))) Z (5/33) hZ (fun j _=>hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (5/33)
        (slotMass (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=>Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

omit [NeZero M] in
private theorem assemblyPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

lemma source_normalized_central_transport (A P C F N : ℂ) (a b v : ℝ)
    (ha : ‖A-P-C‖≤a) (hb : ‖P/N-F‖≤b) (hv : ‖N⁻¹‖≤v) (ha0 : 0≤a) :
    ‖A/N-F-C/N‖≤a*v+b := by
  calc
    _ = ‖(A-P-C)*N⁻¹+(P/N-F)‖ := by congr 1;simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-P-C)*N⁻¹‖+‖P/N-F‖ := norm_add_le _ _
    _ ≤ a*v+b := by rw [norm_mul];gcongr

theorem source_actual_normalized_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=5/33)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := assemblyPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (5/33) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-67/99) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e alpha height/normer‖≤
        C*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e+nu)+Z^(-saving+nu)+
          Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu)+
          Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := source_canonical_probe_exists_ray_cube M H hH K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha (ha.trans_le hab) hB hβ S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := source_actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    (fun j=>hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hprincipal⟩ := ZetaZeroFree.Analytic.Principal.actual_ray_principal_comparison M H hH η S hS
    a b B ellMin ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by linarith) (by linarith)
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨D+Cp,by positivity,?_⟩
  filter_upwards [hcanonical,hnormalizer,hprincipal,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_gt_atTop (0:ℝ)] with Z hcan hnorm hprincipal hdis hZ
  dsimp only at hnorm hprincipal ⊢
  let Yp : Fin K→ℝ := fun j=>Z^(ell j)
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := assemblyPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : ProbePhysical.PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ)≤b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hlabels,hbins,hray,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  refine ⟨hnorm.1,idx,grid,hlabels,hbins,hray,?_⟩
  have hh := source_normalized_central_transport _ _ _ _ _ _ _ _ herror hprincipal.2 hnorm.2 (by positivity)
  apply hh.trans
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e)+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ (HeckeZeroSupremum.beta-67/99-1/25+8*e) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq]
  have h1 : D≤D+Cp := by linarith
  have h2 : Cp≤D+Cp := by linarith
  calc
    _ ≤ (D+Cp)*(Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e+nu)+Z^(-saving+nu))+
      (D+Cp)*(Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu)+Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin)) := by
      gcongr
    _ = _ := by ring

theorem source_actual_normalized_probe_transport_saving (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=5/33)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0<sigma)
    (_hgeometric : sigma+8*e+nu≤1/25) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e≤(7/8)*ellMin) (hlarge : sigma+nu≤saving+157/792) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := assemblyPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (5/33) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-67/99) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-67/99-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,hbound⟩ := source_actual_normalized_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨C,hC,hb⟩ := hbound η
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  dsimp only at hb ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := hb
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,herror.trans ?_⟩
  have h1 : Z^(HeckeZeroSupremum.beta-67/99-1/25+8*e+nu)≤Z^(HeckeZeroSupremum.beta-67/99-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h2 : Z^(-saving+nu)≤Z^(HeckeZeroSupremum.beta-67/99-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h3 : Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu)≤Z^(HeckeZeroSupremum.beta-67/99-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h4 : Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin)≤Z^(HeckeZeroSupremum.beta-67/99-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ C*(4*Z^(HeckeZeroSupremum.beta-67/99-sigma)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = _ := by ring


def sourceCentralBand {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e)
    (η : Character) (Z ζ τ : ℝ) (idx grid : FreeRow→ℕ) : ℂ :=
  finiteCentralCubeRows F.S F.exclusions F.maximal η
    (rowBand (Z^(1/200:ℝ)) (Z^((25/33:ℝ)+ζ))) (F.pools Z)
    (sourcePoolOutside F.modulus ⊤ F.S 1 1 2 (F.lengths Z))
    (fun (_ : Fin 1) y=>(F.w y:ℂ)) (F.lengths Z) F.W F.W
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e
    (fun u=>(51/100:ℝ)+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)

def SourceBins {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e) (η : Character)
    (Z τ : ℝ) (n : ℕ) (idx grid : FreeRow→ℕ) : Prop :=
  (∀u,1 ≤ idx u ∧ idx u≤n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧
    (3*idx u+1:ℕ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
  (∀u,let a : ℝ := 51/100+e*grid u
    51/100≤a ∧ a≤1 ∧
    a≤detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ (by exact le_top) u)) ((3*idx u:ℕ)*Z^τ) ∧
    detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ (by exact le_top) u)) ((3*idx u:ℕ)*Z^τ)<a+e ∧
    detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ (by exact le_top) u)) ((3*(idx u+1):ℕ)*Z^τ)<a+2*e ∧
    (51/100<a → ∃j s,LFunction (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ (by exact le_top) u) j) s=0 ∧
      ¬((sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ (by exact le_top) u) j).residue=1 ∧ s=1) ∧
      a≤s.re ∧ s.re<a+e ∧ |s.im|≤(3*idx u:ℕ)*Z^τ))

theorem source_data_transport_saving {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e)
    (δ ζ saving τ nu sigma : ℝ) (he : 0<e) (he1 : e<1/1000)
    (hδ : 0<δ) (hδ1 : δ≤1/2) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hτ : 0<τ)
    (hnu : 0<nu) (hsigma : 0<sigma) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (hsmall : sigma+8*e+nu≤1/25) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e≤(7/8)*(5/33)) (hlarge : sigma+nu≤saving+157/792) :
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      F.normalizer Z≠0 ∧ ∃idx grid : FreeRow→ℕ,SourceBins F η Z τ n idx grid ∧
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-67/99) Z-sourceCentralBand F η Z ζ τ idx grid/F.normalizer Z‖≤
        C*Z^(HeckeZeroSupremum.beta-67/99-sigma) := by
  obtain ⟨n,hn,htransport⟩ := source_actual_normalized_probe_transport_saving
    F.modulus ⊤ (by exact le_top) 1 e δ 1 2 1 ζ saving τ (5/33) nu
    he he1 hδ hδ1 hζ hζ1 hτ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hnu hβ F.S F.exclusions F.maximal F.first (fun (_ : Fin 1)=>(5/33:ℝ))
    (fun _=>le_rfl) (fun _ _ _=>Subsingleton.elim _ _) (by simp)
    (fun (_ : Fin 1)=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero sigma hsigma hsmall hprincipal hwindow hlarge
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := htransport η
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  dsimp only at hz
  obtain ⟨hnorm,idx,grid,hlabels,hbins,_hray,herror⟩ := hz
  refine ⟨hnorm,idx,grid,⟨hlabels,by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbins⟩,?_⟩
  exact herror


theorem source_data_normalizer_inverse {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e)
    (nu : ℝ) (hnu : 0<nu) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,F.normalizer Z≠0 ∧ ‖(F.normalizer Z)⁻¹‖≤C*Z^nu := by
  exact source_actual_ray_normalizer_inverse F.modulus ⊤ (by exact le_top)
    F.S F.exclusions 1 2 (by norm_num) (by norm_num) (fun (_ : Fin 1)=>(5/33:ℝ))
    (fun _=>by norm_num) (by simp) (fun (_ : Fin 1)=>F.w) (fun _=>F.smooth)
    (fun _=>F.compact) (fun _=>F.support) (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero nu hnu

theorem source_data_error_from_band {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e)
    (δ ζ saving τ nu sigma p : ℝ) (he : 0<e) (he1 : e<1/1000)
    (hδ : 0<δ) (hδ1 : δ≤1/2) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hτ : 0<τ)
    (hnu : 0<nu) (hsigma : 0<sigma) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (hsmall : sigma+8*e+nu≤1/25) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e≤(7/8)*(5/33)) (hlarge : sigma+nu≤saving+157/792)
    (hp : p+nu≤HeckeZeroSupremum.beta-67/99-sigma)
    (hband : ∀n : ℕ,∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      ∀idx grid : FreeRow→ℕ,SourceBins F η Z τ n idx grid →
      ‖sourceCentralBand F η Z ζ τ idx grid‖≤C*Z^p) :
    ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      F.normalizer Z≠0 ∧
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-67/99) Z‖≤C*Z^(HeckeZeroSupremum.beta-67/99-sigma) := by
  obtain ⟨n,_hn,htransport⟩ := source_data_transport_saving F δ ζ saving τ nu sigma he he1
    hδ hδ1 hζ hζ1 hτ hnu hsigma hβ hsmall hprincipal hwindow hlarge
  obtain ⟨D,hD,hinv⟩ := source_data_normalizer_inverse F nu hnu
  intro η
  obtain ⟨C,hC,hbound⟩ := htransport η
  obtain ⟨B,hB,hcentral⟩ := hband n η
  refine ⟨C+B*D,by positivity,?_⟩
  filter_upwards [hbound,hinv,hcentral,eventually_ge_atTop (1:ℝ)] with Z hz hi hc hZ
  obtain ⟨hnorm,idx,grid,hbins,herror⟩ := hz
  refine ⟨hnorm,?_⟩
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hcentralNorm : ‖sourceCentralBand F η Z ζ τ idx grid/F.normalizer Z‖≤
      B*D*Z^(HeckeZeroSupremum.beta-67/99-sigma) := by
    rw [div_eq_mul_inv,norm_mul]
    calc
      _ ≤ (B*Z^p)*(D*Z^nu) := mul_le_mul (hc idx grid hbins) hi.2 (norm_nonneg _) (by positivity)
      _ = B*D*Z^(p+nu) := by rw [Real.rpow_add hZ0 p nu];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hp) (by positivity)
  calc
    _ ≤ ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-67/99) Z-sourceCentralBand F η Z ζ τ idx grid/F.normalizer Z‖+
        ‖sourceCentralBand F η Z ζ τ idx grid/F.normalizer Z‖ :=
      by
        simpa only [sub_add_cancel] using norm_add_le
          (F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
            (sourceCorrection η F.S) (-67/99) Z-sourceCentralBand F η Z ζ τ idx grid/F.normalizer Z)
          (sourceCentralBand F η Z ζ τ idx grid/F.normalizer Z)
    _ ≤ C*Z^(HeckeZeroSupremum.beta-67/99-sigma)+B*D*Z^(HeckeZeroSupremum.beta-67/99-sigma) :=
      add_le_add herror hcentralNorm
    _ = _ := by ring

end
end ZetaZeroFree.Analytic.Probe
