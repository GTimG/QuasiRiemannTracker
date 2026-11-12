/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/{InitialOverlapFourier,
InitialOverlapSource,InitialCommonProfile,InitialCommonCutoff,InitialCommonTransform,
InitialExcludedFourier,InitialResidualTupleEnergy}.lean` (Apache-2.0), via
`Inverse/Init/ResidualTuple.lean`. Modified by Sil (2026-11-12): injective mark `primeMarkInj`;
the residual tuple sum runs over the `PiOK` tuples `(I.pi L).filter (PiOK I j)` (injective, no
entry dividing `j`; `Inj/Dict/Split`), so the lists may overlap (no `PairwiseDisjoint`); the
admissibility / outside hypotheses and the column cover are required on that domain only; the
pairwise coprimality of the entries is derived from injectivity (distinct primes) instead of
being assumed; on the columns seen by the input row (coprime to `j`) the `PiOK` coefficient equals
the one of all injective tuples, which is `primeMarkInj` on the pool; injective oracle
`GoodEnergyExistsInj`. Proofs otherwise unchanged. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Init.Energy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialResidualTupleEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapSource
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Dict.Split

/-!
# Inverse.Inj.Init.ResidualTuple — eighth file of the initialization chain for the injective mark

* `injTuples I L` (injective tuples of `I.pi L`), `primeMarkInj_eq_injTuples`;
* Fourier separation of the injective tuple sum: `markInj_phase`,
  `overlap_tuple_separation_inj`, `actual_overlap_separation_inj`;
* pool reindexing `primeMarkInj_image`, `pool_markInj_active`; `injTuple_coprime`;
* `common_profile_separation_inj`, `tupleProfileInj`, `tupleProfileInj_insert_fresh`,
  `original_profile_point_inj`;
* `PiOK` domain: `piOK_residual_coeff`, `inputRow_coprime_congr`,
  `original_tuples_excluded_fourier_inj` (tuple sum over `(I.pi L).filter (PiOK I j)`);
* **`original_residual_tuple_energy_of_oracle_inj`**.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open FirstPassCubeLabels FirstCauchyArithmetic
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
open InverseInitialOverlapIdealFourier InverseInitialOverlapSource InverseInitialOverlapInputFourier
open InverseInitialKernelBridge InverseInitialLargePool InverseInitialExcludedForcing
open Qrh.MarkedAnchor.Inverse
local notation "O"=>ActualEisensteinCubic.O

section Generic
variable {σ ι : Type*} [DecidableEq ι]

/-- The injective tuples of `I.pi L` (the tuples counted by `primeMarkInj`). -/
def injTuples (I : Finset σ) (L : σ → Finset ι) : Finset (∀ i ∈ I, ι) :=
  (I.pi L).filter (fun p => ∀ i (hi : i ∈ I) j (hj : j ∈ I), p i hi = p j hj → i = j)

theorem mem_injTuples {I : Finset σ} {L : σ → Finset ι} {p : ∀ i ∈ I, ι} :
    p ∈ injTuples I L ↔
      p ∈ I.pi L ∧ ∀ i (hi : i ∈ I) j (hj : j ∈ I), p i hi = p j hj → i = j := by
  unfold injTuples
  rw [Finset.mem_filter]

theorem injTuples_mem_lists {I : Finset σ} {L : σ → Finset ι} {p : ∀ i ∈ I, ι}
    (hp : p ∈ injTuples I L) : ∀ i (hi : i ∈ I), p i hi ∈ L i :=
  Finset.mem_pi.mp (mem_injTuples.mp hp).1

theorem mem_injTuples_of {I : Finset σ} {L : σ → Finset ι} {p : ∀ i ∈ I, ι}
    (h : ∀ i (hi : i ∈ I), p i hi ∈ L i)
    (hinj : ∀ i (hi : i ∈ I) j (hj : j ∈ I), p i hi = p j hj → i = j) : p ∈ injTuples I L :=
  mem_injTuples.mpr ⟨Finset.mem_pi.mpr h, hinj⟩

theorem primeMarkInj_eq_injTuples (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) :
    primeMarkInj I L a A =
      ∑ p ∈ injTuples I L, ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by
  unfold primeMarkInj
  exact Finset.sum_congr (by ext q; rw [mem_injTuples, Finset.mem_filter]) (fun _ _ => rfl)

theorem markInj_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMarkInj I L (fun i p=>a i p*logPhase (-t) (y i p)) A =
      ∑p∈injTuples I L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  rw [primeMarkInj_eq_injTuples]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_tuple_separation_inj (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    (∑p∈injTuples I L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        primeMarkInj I L (fun i p=>a i p*logPhase (-t) (y i p)) A := by
  simp_rw [markInj_phase]
  simp only [Finset.mul_sum,density]
  have he (p : ∀i∈I,ι) (t:ℝ) :
      (𝓕 g) t*logPhase t xj*logPhase t xc*
        ((∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
          logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property))) =
      (𝓕 g) t*logPhase t (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))*
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) := by
    rw [←phase_sub]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun p hp=>fourier_phase_integrable g _ _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_mul_const]
  have hinv := schwartz_logPhase_inversion g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
  rw [mul_comm (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)]
  congr 1
  rw [hinv]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem actual_overlap_separation_inj
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (hy : ∀i∈I,∀p∈L i,0<y i p) (A : Finset ι)
    (yj yc : ℝ) (hj : 0<yj) (hc : 0<yc) :
    (∑p∈injTuples I L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      W (yj*yc/(∏i∈I.attach,y i.val (p i.val i.property)))) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        logPhase t (Real.log yc)*
        primeMarkInj I L (fun i p=>a i p*logPhase (-t) (Real.log (y i p))) A := by
  rw [←overlap_tuple_separation_inj]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := injTuples_mem_lists hp
  congr 1
  simp only [CubicReflectionKernel.logSchwartz_apply,Real.exp_sub,Real.exp_add,
    Real.exp_log hj,Real.exp_log hc,Real.exp_sum]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hy i.val i.property (p i.val i.property) (hp' i.val i.property))).symm

/-- Reindexing the injective mark along an injective map of the prime labels. -/
theorem primeMarkInj_image {κ : Type*} [DecidableEq κ] (f : κ → ι) (hf : Function.Injective f)
    (I : Finset σ) (L : σ → Finset κ) (a : σ → ι → ℂ) :
    ∀ B : Finset κ, primeMarkInj I (fun i => (L i).image f) a (B.image f) =
      primeMarkInj I L (fun i x => a i (f x)) B := by
  induction I using Finset.induction_on with
  | empty => intro B; rw [primeMarkInj_empty, primeMarkInj_empty]
  | insert i I hi ih =>
    intro B
    rw [primeMarkInj_insert I i hi, primeMarkInj_insert I i hi]
    rw [Finset.sum_image (fun x _ y _ h => hf h)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hmem : (f x ∈ B.image f) ↔ x ∈ B := by
      constructor
      · intro h
        obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp h
        rwa [← hf hzx]
      · intro h
        exact Finset.mem_image_of_mem f h
    have herase : (B.image f).erase (f x) = (B.erase x).image f := by
      ext w
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hne, z, hz, rfl⟩
        exact ⟨z, ⟨fun h => hne (h ▸ rfl), hz⟩, rfl⟩
      · rintro ⟨z, ⟨hzx, hz⟩, rfl⟩
        exact ⟨fun h => hzx (hf h), z, hz, rfl⟩
    rw [herase, ih]
    simp only [hmem]

end Generic

/-- Distinct prime ideals are coprime. -/
theorem prime_ideal_isCoprime {P Q : Ideal O} (hP : Prime P) (hQ : Prime Q) (h : P ≠ Q) :
    IsCoprime P Q := by
  let : P.IsPrime := Ideal.isPrime_of_prime hP
  let : Q.IsPrime := Ideal.isPrime_of_prime hQ
  let : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP.ne_zero
  let : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ.ne_zero
  exact Ideal.isCoprime_of_isMaximal h

section Ideal
variable {σ:Type*}

/-- The entries of an injective tuple of primes are pairwise coprime. -/
theorem injTuple_coprime {I : Finset σ} {L : σ → Finset (Ideal O)}
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) {q : ∀ i ∈ I, Ideal O} (hq : q ∈ injTuples I L) :
    Pairwise (Function.onFun IsCoprime (fun i : I => q i.val i.property)) := by
  have hinj := (mem_injTuples.mp hq).2
  have hpi' := injTuples_mem_lists hq
  intro i k hik
  have hne : q i.val i.property ≠ q k.val k.property :=
    fun h => hik (Subtype.ext (hinj _ _ _ _ h))
  exact prime_ideal_isCoprime (hL i.val i.property _ (hpi' i.val i.property))
    (hL k.val k.property _ (hpi' k.val k.property)) hne

/-- The pool-indexed injective mark is the ideal-indexed one on the active primes. -/
theorem pool_markInj_active (F : Finset (Ideal O)) (I : Finset σ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) (a : σ → Ideal O → ℂ) (A : Finset (primePool F)) :
    primeMarkInj I (fun i => poolList F (L i)) (fun i q => a i q.val) A =
      primeMarkInj I L a (activeIndices id I L (∏ i ∈ A, i.val)) := by
  refine (primeMarkInj_image Subtype.val Subtype.val_injective I
    (fun i => poolList F (L i)) a A).symm.trans ?_
  apply primeMarkInj_congr'
  intro i hi
  have hd := dividing_list_image F (L i) (hL i hi) A
  ext P
  rw [Finset.mem_inter, Finset.mem_inter]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h2
    have hxy : y = x := Subtype.val_injective hyx
    subst hxy
    have hm : y.val ∈ (L i).filter (fun P => P ∣ ∏ i ∈ A, i.val) := by
      rw [← hd]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, hy⟩)
    obtain ⟨hmL, hmd⟩ := Finset.mem_filter.mp hm
    exact ⟨hmL, (activeIndices_mem id I L _ hi hmL).mpr hmd⟩
  · rintro ⟨hPL, hPa⟩
    have hm : P ∈ (L i).filter (fun P => P ∣ ∏ i ∈ A, i.val) :=
      Finset.mem_filter.mpr ⟨hPL, (activeIndices_mem id I L _ hi hPL).mp hPa⟩
    rw [← hd] at hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_image_of_mem _ hx1, Finset.mem_image_of_mem _ hx2⟩

theorem common_profile_separation_inj
    (W:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal O))(I:Finset σ)(L:σ→Finset (Ideal O))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal O→ℂ)
    (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(A:Finset (primePool F))
    (yj yc:ℝ)(hj:0<yj)(hc:0<yc) :
    (∑q∈injTuples I L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if survivingProduct I q∣(∏i∈A,i.val) then
        W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log yj) t*logPhase t (Real.log yc)*
        primeMarkInj I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A := by
  have hm (t:ℝ) : primeMarkInj I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A =
      primeMarkInj I L (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P)))
        (activeIndices id I L (∏i∈A,i.val)) :=
    pool_markInj_active F I L hL
      (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P))) A
  simp_rw [hm]
  have he := actual_overlap_separation_inj W a₀ b₀ ha₀ hs hW I L a (slotRatio Z ell)
    (fun i hi P hP=>slotRatio_pos Z hZ ell i (hL i hi P hP))
    (activeIndices id I L (∏i∈A,i.val)) yj yc hj hc
  rw [←he]
  apply Finset.sum_congr rfl
  intro q hq
  have hpi := injTuples_mem_lists hq
  have hprod : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L (∏i∈A,i.val)
      then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣(∏i∈A,i.val) then
        ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣(∏i∈A,i.val) then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property (hpi i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q (∏i∈A,i.val) (injTuple_coprime hL hq) using 1
  rw [hprod]
  split_ifs <;> simp

/-- The injective tuple profile (`InverseInitialCommonCutoff.tupleProfile` on `injTuples`). -/
def tupleProfileInj (I:Finset σ)(L:σ→Finset (Ideal O))(a:σ→Ideal O→ℂ)
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal O) : ℂ :=
  ∑q∈injTuples I L,(∏i∈I.attach,a i.val (q i.val i.property))*
    (if survivingProduct I q∣c then
      W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)

theorem tupleProfileInj_insert_fresh
    (I:Finset σ)(L:σ→Finset (Ideal O))(a:σ→Ideal O→ℂ)
    (Z:ℝ)(ell lo hi:σ→ℝ)(W wFresh:ℝ→ℂ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hc:0<yc)(c:Ideal O) :
    wFresh yc*tupleProfileInj I L a Z ell W yj yc c=tupleProfileInj I L a Z ell W yj yc c := by
  unfold tupleProfileInj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hpi := injTuples_mem_lists hq
  by_cases hz : (∏i∈I.attach,a i.val (q i.val i.property))=0
  · simp only [hz,zero_mul,mul_zero]
  by_cases hd : survivingProduct I q∣c
  swap
  · simp only [hd,ite_false,mul_zero]
  rw [ite_eq_left hd]
  by_cases hw : W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property)))=0
  · simp only [hw,mul_zero]
  have hcoord : ∀i∈I,tupleCoordinate I (slotRatio Z ell) q i∈Set.Icc (lo i) (hi i) := by
    intro i hi'
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi'⟩ (Finset.mem_attach _ _)
    simpa only [tupleCoordinate,dite_eq_left hi'] using ha i hi' (q i hi') (hpi i hi') hn
  have hf := hFresh (tupleCoordinate I (slotRatio Z ell) q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  rw [hf,one_mul]

theorem original_profile_point_inj
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal O))(I:Finset σ)(L:σ→Finset (Ideal O))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal O→ℂ)
    (Z:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A:Finset (primePool F))(yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hjpos:0<yj)(hc:0<yc) :
    tupleProfileInj I L a Z ell W yj yc (∏i∈A,i.val)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (primeMarkInj I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
          childLogTest wFresh t yc) := by
  have he := common_profile_separation_inj W a₀ b₀ ha₀ hs hW F I L hL a Z hZ ell A yj yc hjpos hc
  have hcut := tupleProfileInj_insert_fresh I L a Z ell lo hi W wFresh jlo jhi ha hFresh
    yj yc hj hc (∏i∈A,i.val)
  rw [←hcut]
  unfold tupleProfileInj
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold childLogTest
  ring

end Ideal

section Residual
variable {σ:Type*} [DecidableEq σ]

/-- On a column `A` none of whose primes divides `j`, the residual coefficient of the `PiOK`
tuples (injective, avoiding `j`) is that of all injective tuples. -/
theorem piOK_residual_coeff (I : Finset σ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P) (j : Ideal O) (hj0 : j ≠ 0)
    (F : Finset (Ideal O)) (A : Finset (primePool F)) (hA : ∀ i ∈ A, ¬ i.val ∣ j)
    (c w : (∀ i ∈ I, Ideal O) → ℂ) :
    (∑ q ∈ (I.pi L).filter (PiOK I j),
      c q * (if residual (j*survivingProduct I q) j ∣ (∏ i ∈ A, i.val) then w q else 0)) =
    ∑ q ∈ injTuples I L,
      c q * (if residual (j*survivingProduct I q) j ∣ (∏ i ∈ A, i.val) then w q else 0) := by
  apply Finset.sum_subset
  · intro q hq
    obtain ⟨hpi, hok⟩ := Finset.mem_filter.mp hq
    exact mem_injTuples_of (Finset.mem_pi.mp hpi) hok.1
  · intro q hq hq'
    have hinj := (mem_injTuples.mp hq).2
    have hmem := injTuples_mem_lists hq
    have hex : ∃ k, ∃ hk : k ∈ I, q k hk ∣ j := by
      by_contra hne
      push_neg at hne
      exact hq' (Finset.mem_filter.mpr ⟨Finset.mem_pi.mpr hmem, hinj, hne⟩)
    obtain ⟨k, hk, hkj⟩ := hex
    rw [actual_residual_product I q j hj0]
    have hnd : ¬ survivingProduct I q ∣ (∏ i ∈ A, i.val) := by
      intro hd
      have hks : q k hk ∣ survivingProduct I q := by
        unfold survivingProduct
        exact Finset.dvd_prod_of_mem (s := I.attach)
          (f := fun i : {x // x ∈ I} => q i.val i.property) (a := ⟨k, hk⟩)
          (Finset.mem_attach I ⟨k, hk⟩)
      have hkP := hL k hk _ (hmem k hk)
      have hkA : q k hk ∣ ∏ i ∈ A, i.val := hks.trans hd
      obtain ⟨i, hi, hki⟩ := (hkP.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hkA
      have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
      have he := prime_dvd_prime_eq hkP hip hki
      apply hA i hi
      rw [← he]
      exact hkj
    rw [if_neg hnd, mul_zero]

/-- The input row only sees the columns coprime to `j`. -/
theorem inputRow_coprime_congr (F : Finset (Ideal O)) (hF : ∀ c ∈ F, Admissible c)
    [∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal]
    (Ψ : O →* ℂ) (j : Ideal O) (hj : Admissible j) (u : O)
    (G G' : Finset (primePool F) → ℂ)
    (h : ∀ A : Finset (primePool F), (∀ i ∈ A, ¬ i.val ∣ j) → G A = G' A) :
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ
        (primaryGenerator j) 1 1 G u =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ
        (primaryGenerator j) 1 1 G' u := by
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : ∀ i ∈ A, ¬ i.val ∣ j
  · dsimp only
    rw [h A hA]
  · push_neg at hA
    obtain ⟨i, hi, hd⟩ := hA
    have hgen : Ideal.span {primaryGenerator j} = j :=
      (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
    have hmem : primaryGenerator j ∈ j := by
      have hh := Ideal.mem_span_singleton_self (primaryGenerator j)
      rwa [hgen] at hh
    have hm : rowCoprimeMask (fun i : primePool F => Ideal.span {poolPrimary F i}) A
        (primaryGenerator j) = 0 := by
      unfold rowCoprimeMask
      refine if_pos ⟨i, hi, ?_⟩
      show primaryGenerator j ∈ Ideal.span {poolPrimary F i}
      rw [poolPrimary_span F hF i]
      exact Ideal.dvd_iff_le.mp hd hmem
    simp only [hm, mul_zero, zero_mul]

theorem original_tuples_excluded_fourier_inj
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→Finset (Ideal O))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal O→ℂ)(j:Ideal O)(hjA:Admissible j)
    (hP:∀q∈(I.pi L).filter (PiOK I j),Admissible (j*survivingProduct I q))
    (hPE:∀q∈(I.pi L).filter (PiOK I j),outside E (j*survivingProduct I q))
    (η:Ideal O→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:O)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal O))(hF:∀c∈F,Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) ((I.pi L).filter (PiOK I j))
      (fun q:∀i∈I,Ideal O=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal O=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈(I.pi L).filter (PiOK I j),(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMarkInj I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hj0 : j≠0 := hjA.1
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMarkInj I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (overlap_mode_integrable_inj g I (fun i=>poolList F (L i)) (fun i q=>a i q.val)
      (fun i q=>Real.log (slotRatio Z ell i q.val)) A
      (Real.log ((j.absNorm:ℝ)/Z^G)) (Real.log (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈injTuples I L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point_inj W wFresh a₀ b₀ ha₀ hs hW F I L hL a Z hZ ell lo hi jlo jhi
      ha hFresh A ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  have hpoint' : ∀ A:Finset (primePool F),(∀ i∈A,¬ i.val∣j)→
      (∑q∈(I.pi L).filter (PiOK I j),(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t :=
    fun A hA=>(piOK_residual_coeff I L hL j hj0 F A hA
      (fun q=>∏i∈I.attach,a i.val (q i.val i.property))
      (fun q=>residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))).trans (hpoint A)
  rw [original_tuples_excluded_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2) E hE
    ((I.pi L).filter (PiOK I j)) P j hP (fun q _=>dvd_mul_right j _) hPE F hF hFE hsub η hη
    (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈(I.pi L).filter (PiOK I j),(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [inputRow_coprime_congr F hF (elementCharacter η) j hjA u
    (fun A=>∑q∈(I.pi L).filter (PiOK I j),(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))
    (fun A=>∫t:ℝ,H A t) hpoint']
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end Residual

theorem original_residual_tuple_energy_of_oracle_inj
    (Woriginal W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^Lp≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let _p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let _hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈L i,Hslot i≤2*(P.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
    ∀(lo hi:σ→ℝ)(jlo jhi:ℝ),
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc jlo jhi→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (lo i) (hi i))→
      (∀v:σ→ℝ,∀yj yc:ℝ,(∀i∈all\assigned,v i∈Set.Icc (lo i) (hi i))→
        yj∈Set.Icc jlo jhi→0<yc→Woriginal (yj*yc/(∏i∈all\assigned,v i))≠0→W yc=1)→
      (∀t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
      tupleColumns (originalOutside (originalSource Z r bo) (reflectionExcludedPrimes q))
        (((all\assigned).pi L).filter (PiOK (all\assigned) j)) (fun t=>j*survivingProduct (all\assigned) t) j⊆F→
    ∀hv:ℝ,0≤hv→
      (∀t:ℝ,Adm q Dpool σ (all\assigned) (fun i=>poolList F (L i)) Hslot
        (fun i P=>coeff i P.val*FourierBridge.logPhase (-t) (Real.log (slotRatio Z z i P.val))) Z (hv+|t|))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨Btree,hBtree,henergy⟩:=original_fourier_energy_bound_inj
    (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo)
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨J,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK L Hslot coeff hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent rows hrows
    j hj hspan lo hi jlo jhi hjratio hL hcoeff hFresh hP hPE hsub hv hv0 hadm θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK
    (fun i=>poolList F (L i)) Hslot (fun i P=>coeff i P.val) hHs
    (fun i hi P hP=>hPs i hi P.val (Finset.mem_filter.mp hP).2)
    (fun i hi P hP=>hac i hi P.val (Finset.mem_filter.mp hP).2)
    qelem z al bl primeW hz hqe hprimeW hprimeLive (elementCharacter χ) hχ hperiod
    D m r hm hmcap hDlo hprodj hprod hlow (fun i hi P hP=>hHlow i hi P.val (Finset.mem_filter.mp hP).2) hKη hDeq hr0 hrP hzS hm1 hparent rows hrows
    (fun i P=>Real.log (slotRatio Z z i P.val)) (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) θ hv hv0 hadm
  have hsum:∑i∈all\assigned,z i=assignedCenter all z-assignedCenter assigned z:=by
    have hh:=Finset.sum_sdiff (f:=z) hassigned
    dsimp [assignedCenter]
    linarith
  have hgj:Ideal.span {primaryGenerator j}=Ideal.span {assignedElement assigned qelem}:=
    (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1.trans hspan.symm
  have hid (u:O):
      (∑t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),(∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u)=
      ∫t:ℝ,density (frequencyTwist (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo) θ)
        (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ (elementCharacter χ)
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMarkInj (all\assigned) (fun i=>poolList F (L i))
            (fun i P=>coeff i P.val*logPhase (-t) (Real.log (slotRatio Z z i P.val))))
            (childLogTest W t) Z D) u):=by
    have hh:=original_tuples_excluded_fourier_inj
      (childLogTest Woriginal θ) W ao bo hao
      ((InverseInitialOriginalHeight.child_support Woriginal θ).trans hso)
      (InverseInitialOriginalHeight.child_smooth Woriginal ao bo hao hso hWo θ)
      (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (all\assigned) L hL coeff j hj hP hPE χ hout u Z r
      (assignedCenter all z) (assignedCenter assigned z) hZp z lo hi hsum jlo jhi hjratio hcoeff
      (fun v yj yc hv hyj hyc hn=>hFresh v yj yc hv hyj hyc
        (InverseInitialOriginalHeight.child_support Woriginal θ hn))
      F hFa (fun I hI=>(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2) hsub
    rw [hh,InverseInitialOriginalHeight.logSchwartz_child]
    simp only [←hDeq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [InverseInitialInputReindex.input_puncture_span p hg Finset.univ (elementCharacter χ)
      (primaryGenerator j) (assignedElement assigned qelem) hgj]
  simpa only [hid] using he

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.original_tuples_excluded_fourier_inj
#print axioms Qrh.MarkedAnchor.Inverse.Inj.original_residual_tuple_energy_of_oracle_inj
