/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from hailey_collet_1252270103 `Record12518109Gain/Upstream/DeletionInverse.lean`
(`deleted_direct_energy`, `direct_reference_energy`; itself adapted from PR63
gao-balanced-marked-20261017) and openai_baseline `Dictionary/InverseMarkedReferencePaddedEnergy.lean`
(Apache-2.0). Modified by Sil (2026-11-11): the native reserve padding (`exists_reserve`,
`shifted_capacity`, ball `1+ρ`) is dropped (ball `m = 1`, shifted free width `rr ∈ [r-η, r]`
stays in the parent rectangle) and `original_source_energy` is replaced by
`original_source_energy_of_oracle`. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.SourceEnergy
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.NativeBridge

/-!
# Inverse.Init.DirectEnergy — top of the oracle-parametric initialization chain

`direct_energy_of_oracle`: the actual inverse marked moment
`∑_u ‖polynomial (data.character u) true (childLogTest W θ) (U^r) 0 0 * ∏ directSlot …‖²` on the
unit row ball, for every slot vector with `r ≤ Pmax`, `∑ ell ≤ Smax` (parent rectangle,
`Pmax + Smax ≤ 1`), bounded by `C U^(1+18η)`, from the canonical oracle on
`InitState Pmax Smax κ` (`9η ≤ κ`, `η ≤ lag`), for slot vectors whose dictionary images pass
`Adm`. No native gate is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseRawConjugateGates
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open ConcreteTraceCRT InverseMoment InverseInitialProfile InverseInitialRawDictionary
open InverseInitialConjugateEnergy InverseInitialMarkedDictionary
open InverseInitialPhysicalSlots InverseInitialExcludedPeriod InverseInitialPoissonBridge
open InverseInitialEnergyCallerWindow
open IdealMobiusDivisorSum
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- The dictionary image of a slot vector must pass `Adm` (for every assigned set `J`, every pool
bound and every log-phase twist). -/
def DirectAdm (Adm : SlotAdm) (data : RowData) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (U hv : ℝ) : Prop :=
  ∀ (J : Finset ι) (Dpool : ℕ) (t : ℝ),
    Adm (deletedPeriod (basePeriod data)) Dpool ι (Finset.univ \ J)
      (fun i => InverseInitialCommonLists.poolList
        (InitialMeanSquare.outsideSquarefreeIdeals
          (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool) (L i))
      (fun i => 2*U^(ell i))
      (fun i P => star (β i P.val / idealCoeff (deletedBase data) P.val) *
        FourierBridge.logPhase (-t)
          (Real.log (InverseInitialCommonProfile.slotRatio U ell i P.val))) U (hv+|t|)

theorem direct_energy_of_oracle (W : ℝ → ℂ) (ao bo : ℝ) (hao : 0<ao)
    (hab : ao≤bo) (hsW : Function.support W⊆Icc ao bo) (hW : ContDiff ℝ ∞ W)
    (Adm : SlotAdm) (Pmax Smax κ eta : ℝ) (hP0 : 0 ≤ Pmax) (hS0 : 0 ≤ Smax)
    (hPS : Pmax+Smax ≤ 1) (heta : 0 < eta) (heta7 : 7*eta ≤ 1) (hκ : 9*eta ≤ κ)
    (K : ℕ)
    (horacle : ∀ (Wf : 𝓢(ℝ,ℂ)) (lf hf : ℝ), 0 < lf → lf ≤ hf →
      Function.support (Wf : ℝ → ℂ) ⊆ Icc lf hf →
      GoodEnergyExists Adm (InitState Pmax Smax κ) eta 3 K Wf) :
    ∀ data : RowData, ∃ (degree : ℕ) (C U₀ : ℝ), 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤1) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀ hv : ℝ, 0 ≤ hv → DirectAdm Adm data L ell β U hv →
      ∀r : ℝ, 0≤r → r≤Pmax → (∑i,ell i)≤Smax →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) → ∀θ : ℝ,
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W θ) (U^r) 0 0 *
          (∏i,directSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 := by
  have henergy := original_source_energy_of_oracle W ao bo hao hab hsW hW
    Adm Pmax Smax κ 3 eta eta eta eta eta heta heta heta (by linarith) heta
    (by linarith) le_rfl heta K horacle
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩ := raw_conjugate_base_gates data
  obtain ⟨degree,C,U₀,hC,hU₀,henergy⟩ := henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩ := eventually_atTop.mp (marked_shift_eventually data eta heta)
  have hev : ∀ᶠ U : ℝ in atTop, (2:ℝ)^K ≤ U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  obtain ⟨Uscale,hscale⟩ := eventually_atTop.mp hev
  let divs := idealDivisors (∏P∈excluded data,P)
  refine ⟨degree,((divs.card : ℝ)+1)^2*C,max U₀ (max Ushift Uscale),by positivity,
    lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hdis hratio hβ hlarge hv hv0 hadm r hr hrP hSm rows
    hrows θ
  have hU0 : U₀≤U := (le_max_left _ _).trans hU
  have hUone : 1<U := hU₀.trans_le hU0
  have hUp : 0<U := zero_lt_one.trans hUone
  have hpow : (2:ℝ)^K ≤ U^eta := hscale U (((le_max_right _ _).trans (le_max_right _ _)).trans hU)
  have hS0' : 0 ≤ ∑i,ell i := Finset.sum_nonneg (fun i _ => hell i)
  have hg (i : ι) (P : Ideal O) (hP : P∈L i) :=
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.deleted_prime_gates data P
      (hp i P hP) ((hlarge i).trans_le
      (by simpa only [one_mul] using
        (le_div_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio i P hP).1))
  let coeff := fun i P => β i P / idealCoeff (deletedBase data) P
  have hc (i : ι) (P : Ideal O) (hP : P∈L i) : ‖coeff i P‖≤1 := by
    dsimp [coeff]
    rw [norm_div,(hg i P hP).2.2.1,div_one]
    exact hβ i P hP
  let marker : ℝ → ℂ := (Icc (1 : ℝ) 2).indicator (fun _=>1)
  have hm : Function.support marker⊆Icc (1 : ℝ) 2 := Set.support_indicator_subset
  have hlive (i : ι) (P : Ideal O) (hP : P∈L i) : marker ((P.absNorm : ℝ)/U^(ell i))≠0 := by
    simp [marker,hratio i P hP]
  let rawRows := rows.image (fun u=>u.val)
  have hrawRows (u : O) (hu : u∈rawRows) : ‖eisEmbedding u‖^2≤U^(1:ℝ) := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    rw [Real.rpow_one]
    exact hrows v hv
  have hsupport : ∀x,childLogTest W θ x≠0 → x≤bo := by
    intro x hx
    exact (hsW (by intro hz;exact hx (by simp [childLogTest,hz]))).2
  let mark := fun u : NonzeroElement => ∏i,directSlot u.val (L i) (β i) (U^(ell i))
  have hd := marked_fixed_deletion data rows (childLogTest W θ) (U^r) 0 0 bo
    (Real.rpow_pos_of_pos hUp _) hsupport mark
  have hjbound (j : Ideal O) (hj : j∈divs) :
      (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true (childLogTest W θ)
        (U^r/(j.absNorm : ℝ)) 0 0 * mark u‖^2) ≤
        C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 := by
    have hjshift := (hshift U (((le_max_left _ _).trans (le_max_right _ _)).trans hU)).2 j hj r
    have hscaleU : U^(shiftedExponent data U r j) = U^r/(j.absNorm : ℝ) := hjshift.2.2
    have hGJ (J : Finset ι) : (∑i∈J,ell i) ≤ ∑i,ell i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hell i)
    have hGJ0 (J : Finset ι) : 0 ≤ ∑i∈J,ell i := Finset.sum_nonneg (fun i _ => hell i)
    have he := henergy U hU0 hpow hK L ell coeff hell hp
      (fun i P hP=>(hg i P hP).2.2.2) hdis hratio hc
      (fun i P hP=>by rw [hqset];exact (hg i P hP).1)
      (fun _=>marker) (fun _=>hm) hlive
      (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
      hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
      hv hv0 hadm 1 (shiftedExponent data U r j) zero_le_one (by norm_num)
      (fun J => by have := hGJ J; have := hGJ0 J; linarith [hjshift.1])
      hP0 (hjshift.2.1.trans hrP) hSm le_rfl (by linarith [hjshift.2.1])
      rawRows hrawRows θ
    rw [Finset.sum_image (fun u _ v _ he=>Subtype.ext he)] at he
    rw [← hscaleU]
    convert he using 1
    · apply Finset.sum_congr rfl
      intro u _
      have hmk : mark u = ∏i,Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.directPrimeSlot
          u.val (L i) (β i) (U^(ell i)) := rfl
      rw [hmk, Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.deleted_direct_slots_initial
        data u L β ell (childLogTest W θ) U (shiftedExponent data U r j) bo hUp hsupport
        (fun i P hP=>(hg i P hP).2.1)]
    · rw [show (1:ℝ)+15*eta+eta+eta+eta = 1+18*eta by ring]
  apply hd.trans
  change (divs.card : ℝ) * (∑j∈divs,_) ≤ _
  calc
    _ ≤ (divs.card : ℝ) * ∑j∈divs,C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjbound) (by positivity)
    _ = (divs.card : ℝ)^2*C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr <;> linarith

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.direct_energy_of_oracle
