/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.WholeAnchorSlots
import Submissions.hailey_collet_1252270103.LocalMoment.PlainUnmarkedAdapter
import Candidate.Cycle63.Marked.FinitePositiveEnergy
import Candidate.Cycle63.Marked.AnnularPool
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRelativeSlots

namespace Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentDetectorEnergyInitialState CenteredMomentWholeSlotDeletion
open CenteredMomentExceptionalPair HeckeRowClosure CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots LocalMoment
open Cycle61Moment OAI.SevenEighths.Cycle63MarkedPlain
local notation "O" => HeckeFamily.O

/-- Natural rows give the literal initial source element presentation. -/
theorem natural_initial_element (η : Character) (u : O) (hu : u≠0) (n : O) :
    elementCoeff (naturalRow η u hu).character n=
      rowTwist (elementHom η) (fixedBadMask*idealGenerator 1) 1 (1*u) n := by
  have hh := (naturalRow η u hu).masked_element 1 one_ne_zero n
  rw [excluded_element _ (naturalRow η u hu).element_zero 1 one_ne_zero,
    if_pos (isCoprime_one_right)] at hh
  simpa only [one_mul] using hh

/-- The finite common source exception contains every row failing any
source keep predicate; it is independent of scale, roots and slot data. -/
theorem source_exceptions_finite {Label : Type*} [Fintype Label]
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hQ0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hQt : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hQ72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (hQbase : ∀j,internalQ (bad j) (anchor j)≤(base j).modulus) :
    {u : FreeRow | ∃j,¬initialKeep (base j) (internalQ (bad j) (anchor j)) u.val}.Finite := by
  have h : (⋃j,{u : FreeRow | ¬initialKeep (base j) (internalQ (bad j) (anchor j)) u.val}).Finite := by
    apply Set.finite_iUnion
    intro j
    exact fixed_exceptional_free_finite (base j) _ (hQ0 j) (hQt j) (hQ72 j) (hQbase j)
  simpa only [Set.iUnion_ofPred] using h

theorem exists_extraE {Label : Type*} [Fintype Label]
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hQ0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hQt : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hQ72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (hQbase : ∀j,internalQ (bad j) (anchor j)≤(base j).modulus) :
    ∃ E : Finset FreeRow, ∀u, u∉E →
      ∀j,initialKeep (base j) (internalQ (bad j) (anchor j)) u.val := by
  let hfinite := source_exceptions_finite base anchor bad hQ0 hQt hQ72 hQbase
  refine ⟨hfinite.toFinset,?_⟩
  intro u hu j
  by_contra hn
  apply hu
  exact hfinite.mem_toFinset.mpr ⟨j,hn⟩

/-- A fixed auxiliary root cap follows from the original ambient norm and
a positive core-radius cutoff; its exponent is fixed before slot data. -/
theorem root_norm_from_ambient (root : NonzeroIdeal) {Z U bΦ Mcap dmin : ℝ}
    (hZ : 1≤Z) (hd : 0<dmin) (hM : 0≤Mcap) (hPhi : bΦ≤Z)
    (hcore : Z^dmin≤U) (hroot : (root.val.absNorm:ℝ)^6≤bΦ*Z^Mcap) :
    (root.val.absNorm:ℝ)≤U^((Mcap+1)/dmin+1) := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hU1 : 1≤U := (Real.one_le_rpow hZ hd.le).trans hcore
  have hAr : 0≤(Mcap+1)/dmin+1 := by positivity
  have hn : 1≤(root.val.absNorm:ℝ) := by
    have hnat : 0<root.val.absNorm := by
      have hp := HeckeDyadic.norm_pos root
      change (0:ℝ)<(root.val.absNorm:ℝ) at hp
      exact_mod_cast hp
    exact_mod_cast (Nat.succ_le_iff.mpr hnat)
  have hpow : (root.val.absNorm:ℝ)≤(root.val.absNorm:ℝ)^6 :=
    le_self_pow₀ hn (by norm_num)
  have hsmall : (root.val.absNorm:ℝ)≤Z^(Mcap+1) := by
    apply hpow.trans (hroot.trans _)
    calc bΦ*Z^Mcap ≤ Z*Z^Mcap :=
          mul_le_mul_of_nonneg_right hPhi (Real.rpow_nonneg hZp.le _)
      _ = Z^(1:ℝ)*Z^Mcap := by rw [Real.rpow_one]
      _ = Z^((1:ℝ)+Mcap) := (Real.rpow_add hZp _ _).symm
      _ = Z^(Mcap+1) := by congr 1; ring
  apply hsmall.trans
  calc Z^(Mcap+1) ≤ Z^(dmin*((Mcap+1)/dmin+1)) := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh : dmin*((Mcap+1)/dmin)=Mcap+1 := mul_div_cancel₀ _ hd.ne'
        nlinarith
    _ = (Z^dmin)^((Mcap+1)/dmin+1) := Real.rpow_mul hZp.le _ _
    _ ≤ U^((Mcap+1)/dmin+1) := Real.rpow_le_rpow (Real.rpow_nonneg hZp.le _) hcore hAr

/-- The common archimedean slot phase has modulus one. It is retained
here rather than asserted to be an exact equality of the source slots. -/
theorem normalized_annular_norm (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ) (W : ℝ→ℂ)
    (P σ t v : ℝ) (hP : 0<P) :
    ‖normalizedSlot η m A z (primePool M H 2 P)
      (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖ =
    ‖naturalSlot χ (primePool M H 2 P)
      (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ (t+v) I) P‖ := by
  rw [naturalSlot_of_row η χ m A z hrow]
  rw [relative_normalizedSlot_eq_ray M H η χ ν m A z hrow W 2 P σ t v hP,
    relative_normalizedSlot_eq_ray M H η χ ν m A z hrow W 2 P σ 0 (t+v) hP]
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,zero_add,norm_mul]
  rw [CenteredMomentTwist.norm_real_imaginary_power P t hP,one_mul]

/-- Annular filtering preserves the actual normalized physical slot. -/
theorem normalized_annular_filter (η ν : Character) (m A z : O)
    (pool : Finset (Ideal O)) (W : ℝ→ℂ) (hW : Function.support W⊆Icc (1:ℝ) 2)
    (P σ t v : ℝ) :
    normalizedSlot η m A z (annularPool pool P)
      (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P =
    normalizedSlot η m A z pool
      (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P := by
  unfold normalizedSlot rowSlot annularPool
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases ha : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2
  · exact if_pos ha
  · rw [if_neg ha]
    have hz : W ((I.absNorm:ℝ)/P)=0 := by
      by_contra hn
      exact ha (hW hn)
    simp [HeckePrimeAnnular.annularWeight,hz]


theorem natural_excluded_coefficients (η : Character) (R : Ideal O) (hR : R≠0)
    (u : O) (hu : u≠0) (I : Ideal O) :
    idealCoeff (naturalRow (excluded η R) u hu).character I=
      idealCoeff (excluded (naturalRow η u hu).character R) I := by
  rw [(naturalRow (excluded η R) u hu).ideal,excluded_ideal _ _ hR,
    excluded_ideal _ _ hR,(naturalRow η u hu).ideal]
  split_ifs <;> simp

/-- The original rooted physical response has exactly the norm of the
root-punctured source slot, including its common archimedean phase. -/
theorem normalized_root_annular_norm (η ν : Character) (u : O) (hu : u≠0)
    (root : NonzeroIdeal) (M : Ideal O) (H : Subgroup (O⧸M)ˣ) (W : ℝ→ℂ)
    (P σ t v : ℝ) (hP : 0<P) :
    ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 (u*(idealGenerator root.val)^6)
      (primePool M H 2 P)
      (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖=
    ‖naturalSlot (excluded (naturalRow η u hu).character root.val) (primePool M H 2 P)
      (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ (t+v) I) P‖ := by
  rw [RootHoleSlots.normalizedSlot_sixth_root η (fixedBadMask*idealGenerator 1) 1 u
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) root]
  rw [←RootHoleSlots.normalizedSlot_excluded η (fixedBadMask*idealGenerator 1) 1 u
    (primePool M H 2 P) (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I)
    t P root.val root.property]
  rw [normalized_annular_norm (excluded η root.val)
    (naturalRow (excluded η root.val) u hu).character ν (fixedBadMask*idealGenerator 1) 1 u
    (natural_initial_element (excluded η root.val) u hu) M H W P σ t v hP]
  congr 1
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [natural_excluded_coefficients η root.val root.property u hu]


variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def base (η η₀ : Character) : WholeSourceIndex M H→Character :=
  wholeSourceBase M H hH η₀ η

def goodRows (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (rows : Finset FreeRow) : Finset FreeRow :=
  rows.filter (fun u=>∀j,initialKeep (base M H hH η η₀ j)
    (internalQ (bad j) (WholeAnchorSlots.sourceAnchor M H hH η₀ j)) u.val)

/-- The original normalized slot response, with every root and core/root
shared-prime hole retained. -/
def originalSlot {Slot : Type*} (η η₀ : Character) (root : NonzeroIdeal)
    (W : ℝ→ℂ) (U : ℝ) (θ : Slot→RayQuotient.Characters M H)
    (w σ v : Slot→ℝ) (t : ℝ) (u : FreeRow) (s : Slot) : ℂ :=
  normalizedSlot η (fixedBadMask*idealGenerator 1) 1 (u.val*(idealGenerator root.val)^6)
    (primePool M H 2 (U^(w s)))
    (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I) t (U^(w s))

theorem base_modulus (η η₀ : Character) (Q : Ideal O)
    (hη : Q≤η.modulus) (hM : Q≤M) (hη₀ : Q≤η₀.modulus)
    (j : WholeSourceIndex M H) : Q≤(base M H hH η η₀ j).modulus := by
  cases j with
  | inl j => exact hη
  | inr j =>
    change Q≤(η.modulus ⊓ (M ⊓ η₀.modulus)) ⊓ M
    exact le_inf (le_inf hη (le_inf hM hη₀)) hM

theorem anchor_modulus (η₀ : Character) (Q : Ideal O)
    (hM : Q≤M) (hη₀ : Q≤η₀.modulus)
    (j : WholeSourceIndex M H) : Q≤(WholeAnchorSlots.sourceAnchor M H hH η₀ j).modulus := by
  cases j with
  | inl j => exact hη₀
  | inr j =>
    change Q≤(η₀.modulus ⊓ (M ⊓ η₀.modulus)) ⊓ M
    exact le_inf (le_inf hη₀ (le_inf hM hη₀)) hM

/-- One fixed source bad ideal for the entire physical dictionary. -/
def fixedBad (η η₀ : Character) : Ideal O :=
  ((Ideal.span {(72:O)} ⊓ M) ⊓ η₀.modulus) ⊓ η.modulus

theorem fixedBad_gates (η η₀ : Character) :
    fixedBad M η η₀≠0 ∧ fixedBad M η η₀≠⊤ ∧
      fixedBad M η η₀≤Ideal.span {(72:O)} ∧ fixedBad M η η₀≤M ∧
      fixedBad M η η₀≤η₀.modulus ∧ fixedBad M η η₀≤η.modulus := by
  have h72 : (Ideal.span {(72:O)})≠(0:Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)
  have hproper : (Ideal.span {(72:O)})≠(⊤:Ideal O) := by
    intro h
    have hu : IsUnit (72:O) := Ideal.span_singleton_eq_top.mp h
    exact CanonicalRowCompletion.negative_two_prime.not_unit
      (isUnit_of_dvd_unit (show (-2:O)∣72 from ⟨-36,by norm_num⟩) hu)
  have hle72 : fixedBad M η η₀≤Ideal.span {(72:O)} :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  refine ⟨?_,?_,hle72,?_,?_,inf_le_right⟩
  · exact Ideal.inf_ne_bot_of_ne_bot
      (Ideal.inf_ne_bot_of_ne_bot (Ideal.inf_ne_bot_of_ne_bot h72 (NeZero.ne M))
        η₀.modulus_ne_bot) η.modulus_ne_bot
  · intro h
    exact hproper (top_le_iff.mp (h ▸ hle72))
  · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_left.trans inf_le_right

theorem exists_batch_extraE (η η₀ : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (hQη : Q≤η.modulus) (hQM : Q≤M) (hQη₀ : Q≤η₀.modulus) :
    ∃ E : Finset FreeRow, ∀u, u∉E → ∀j : WholeSourceIndex M H,
      initialKeep (base M H hH η η₀ j)
        (internalQ Q (WholeAnchorSlots.sourceAnchor M H hH η₀ j)) u.val := by
  apply exists_extraE (base M H hH η η₀) (WholeAnchorSlots.sourceAnchor M H hH η₀) (fun _=>Q)
  · intro j
    simpa only [internalQ,inf_eq_left.mpr (anchor_modulus M H hH η₀ Q hQM hQη₀ j)] using hQ0
  · intro j
    simpa only [internalQ,inf_eq_left.mpr (anchor_modulus M H hH η₀ Q hQM hQη₀ j)] using hQt
  · intro j
    exact inf_le_left.trans hQ72
  · intro j
    exact inf_le_left.trans (base_modulus M H hH η η₀ Q hQη hQM hQη₀ j)

/-- Concrete rooted batch on the literal original normalized slots.
Only the fixed finite source-exception set is filtered; no moving prime
sector, root/core intersection, ray label or slot is deleted. -/
def batch {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (root : NonzeroIdeal) (W : ℝ→ℂ) (U Aroot : ℝ) (hU : 0<U)
    (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (hroot : (root.val.absNorm:ℝ)≤U^Aroot)
    (rows : Finset FreeRow) (slots : Finset Slot)
    (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (t : ℝ)
    (hw : ∀s∈slots,0≤w s)
    (hσ0 : ∀s∈slots,(33/50:ℝ)≤σ s) (hσ1 : ∀s∈slots,σ s≤33/50)
    (hnorm : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U)
    (hemb : ∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤U) :
    RootedBatch (Slot:=Slot) M H hH (base M H hH η η₀)
      (WholeAnchorSlots.sourceAnchor M H hH η₀) bad W U Aroot where
  rows := goodRows M H hH η η₀ bad rows
  family := fun u j=>(naturalRow (base M H hH η η₀ j) u.val u.property.1).character
  slots := slots
  widths := w
  sigma := σ
  relativeHeight := v
  commonHeight := t
  Q := originalSlot M H hH η η₀ root W U θ w σ v t
  rays := fun _=>θ
  root := fun _=>root.val
  root_ne_zero := fun _=>root.property
  root_norm := fun _=>hroot
  rowNorm := fun u hu=>hnorm u (Finset.mem_filter.mp hu).1
  embeddingNorm := fun u hu=>hemb u (Finset.mem_filter.mp hu).1
  widthsNonneg := hw
  sigmaLower := hσ0
  sigmaUpper := hσ1
  idealCoefficients := by
    intro u hu j I
    exact natural_raw_coefficients _ (momentElement u) I
  elementCoefficients := by
    intro u hu j n
    exact natural_initial_element _ u.val u.property.1 n
  retained := fun u hu j=>(Finset.mem_filter.mp hu).2 j
  plainIdentity := by
    intro u hu j s hs
    dsimp [originalSlot]
    rw [normalized_root_annular_norm η (relativeCharacter M H hH η₀ (θ s))
      u.val u.property.1 root M H W (U^(w s)) (σ s) t (v s) (Real.rpow_pos_of_pos hU _)]
    exact congrArg (fun z : ℂ=>‖z‖) (WholeAnchorSlots.common_slot_root M H hH η η₀ u.val
      u.property.1 j (θ s) root.val root.property (primePool M H 2 (U^(w s)))
      (fun I=>HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t+v s) I) (U^(w s))).symm
  inverseBase := η
  inverseMask := fixedBadMask*idealGenerator 1
  inverseAux := 1
  inverseRoot := idealGenerator root.val
  inversePools := fun s=>annularPool (primePool M H 2 (U^(w s))) (U^(w s))
  inverseCoefficients := fun s=>relativeCharacter M H hH η₀ (θ s)
  inversePrime := by
    intro s hs I hI
    exact (Finset.mem_filter.mp (annularPool_subset _ _ hI)).2.1
  inverseRatios := fun s hs I hI=>annularPool_ratio _ _ _ hI
  inverseIdentity := by
    intro u hu s hs
    exact (normalized_annular_filter η (relativeCharacter M H hH η₀ (θ s))
      (fixedBadMask*idealGenerator 1) 1 (u.val*(idealGenerator root.val)^6)
      (primePool M H 2 (U^(w s))) W hWs (U^(w s)) (σ s) t (v s)).symm

end
end Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- Fixed finite relabeling, including duplication for the two whole
character orientations. It does not alter the original common response. -/
def RootedBatch.reindex {Label Label' Slot : Type*}
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {U Aroot : ℝ}
    (B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot) (index : Label'→Label) :
    RootedBatch (Slot:=Slot) M H hH (base∘index) (anchor∘index) (bad∘index) W U Aroot where
  rows := B.rows
  family := fun u j=>B.family u (index j)
  slots := B.slots
  widths := B.widths
  sigma := B.sigma
  relativeHeight := B.relativeHeight
  commonHeight := B.commonHeight
  Q := B.Q
  rays := fun j=>B.rays (index j)
  root := B.root∘index
  root_ne_zero := fun j=>B.root_ne_zero (index j)
  root_norm := fun j=>B.root_norm (index j)
  rowNorm := B.rowNorm
  embeddingNorm := B.embeddingNorm
  widthsNonneg := B.widthsNonneg
  sigmaLower := B.sigmaLower
  sigmaUpper := B.sigmaUpper
  idealCoefficients := fun u hu j=>B.idealCoefficients u hu (index j)
  elementCoefficients := fun u hu j=>B.elementCoefficients u hu (index j)
  retained := fun u hu j=>B.retained u hu (index j)
  plainIdentity := fun u hu j=>B.plainIdentity u hu (index j)
  inverseBase := B.inverseBase
  inverseMask := B.inverseMask
  inverseAux := B.inverseAux
  inverseRoot := B.inverseRoot
  inversePools := B.inversePools
  inverseCoefficients := B.inverseCoefficients
  inversePrime := B.inversePrime
  inverseRatios := B.inverseRatios
  inverseIdentity := B.inverseIdentity

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete.batch
#print axioms Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete.source_exceptions_finite
#print axioms Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete.normalized_root_annular_norm
