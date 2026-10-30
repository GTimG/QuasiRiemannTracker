/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalCellPackets
import Submissions.arvi_selected_leaf.JointDetector.NaturalPivotTransport
import Submissions.arvi_selected_leaf.JointDetector.NaturalFrequencyReindex
import Submissions.arvi_selected_leaf.JointDetector.NaturalDiagonalMask
import Submissions.arvi_selected_leaf.JointDetector.NaturalPhysicalBudget

/-! Assembly bookkeeping for the literal finite near packets. None of the
intermediate bounds in this file is a replacement for their actual Mellin
transport; the original selectors and source cap remain explicit. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss CenteredExceptionalCount IdealMobiusDivisorSum
open NaturalSharedTables NaturalPairPackets NaturalTupleIdentity
local notation "O" => ActualEisensteinCubic.O

/-- A dual source dyad is capped by BOTH its dyadic upper endpoint and the
original fixed auxiliary height. Only its displayed scalar envelope is
enlarged afterwards. -/
theorem source_norm_clip (rows : Finset O) (S : Finset (Ideal O)) (B T cap δ K : ℝ)
    (hB : 0 ≤ B) (hT : 1 ≤ T) (hcap : 1 ≤ cap) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hnT : ∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ T)
    (hncap : ∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ cap)
    (hbound : ∀ t : ℝ,1 ≤ t → t ≤ cap →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ t) →
      selectedNorm rows S ≤ K*(t+B^(1-δ)*t^δ)) :
    selectedNorm rows S ≤ K*(T+B^(1-δ)*T^δ) := by
  apply (hbound (min T cap) (le_min hT hcap) (min_le_right _ _)
    (fun I hI => le_min (hnT I hI) (hncap I hI))).trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply add_le_add (min_le_left _ _)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hB _)
  exact Real.rpow_le_rpow (by positivity) (min_le_left _ _) hδ

theorem table_mask_card (F : Finset ColourTuple) (g : SharedTable)
    (hgn : ∀ j k,g j k ≠ 0) :
    (tableSourceMask F g).powerset.card ≤ 4*(idealDivisors (diagonalProduct g)).card := by
  have hdiag : diagonalProduct g ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hgn j j)
  have hpowers : (diagonalPrimes F g).powerset.card ≤ (idealDivisors (diagonalProduct g)).card := by
    apply Finset.card_le_card_of_injOn (fun E : Finset (PrimeIndex F) => ∏ i ∈ E,i.val)
    · intro E hE
      exact (mem_idealDivisors hdiag).mpr
        (goodPuncture_divides_diagonal F g E (Finset.mem_powerset.mp hE))
    · intro E hE E' hE' he
      exact FiveColourIncidence.primeSubsetProduct_injective
        (fun i : PrimeIndex F => i.val) (commonPrime_prime F) Subtype.val_injective he
  have hcard : (tableSourceMask F g).card ≤ 2+(diagonalPrimes F g).card := by
    unfold tableSourceMask
    apply (Finset.card_union_le _ _).trans
    apply Nat.add_le_add
    · exact (Finset.card_image_le).trans (by simp)
    · exact Finset.card_image_le
  calc
    _ = 2^(tableSourceMask F g).card := Finset.card_powerset _
    _ ≤ 2^(2+(diagonalPrimes F g).card) := Nat.pow_le_pow_right (by decide) hcard
    _ = 4*(diagonalPrimes F g).powerset.card := by rw [Finset.card_powerset,pow_add]; norm_num
    _ ≤ _ := Nat.mul_le_mul_left _ hpowers

/-- The zero frequency is killed only by the actual offdiagonal primitive
character. Its diagonal principal term is retained by the original Gram. -/
theorem offDiagonal_packetTerm_zero (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (c d : F) (W : 𝓢(ℝ,ℂ)) (L : ℝ) (E : Finset (SourceMaskIndex F)) :
    offDiagonalKeep F c d*NaturalActualTail.packetTerm F hF c.val d.val W L E 0=0 := by
  by_cases he : c=d
  · simp only [offDiagonalKeep,he,ite_true,zero_mul]
  · have hne : c.val ≠ d.val := fun h => he (Subtype.ext h)
    have hz := primitiveRow_zero_offdiagonal F hF c.val d.val c.property d.property
      (hpF c.val c.property) (hpF d.val d.property) hne
    simp only [NaturalActualTail.packetTerm,NaturalActualTail.packetCoefficient,hz,
      star_zero,mul_zero,zero_mul]

/-- Exact finite near-frequency decomposition. The original zero mode is
paid by its proved offdiagonal vanishing before passing to ordinary ideal
sources; all bad-output and unit sectors remain in the displayed sum. -/
theorem tupleNearOffDiagonalGram_eq_sectors (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (a : F → ℂ) (L H : ℝ) (hH : 0 ≤ H) :
    tupleNearOffDiagonalGram F hF a L H=
      ∑ c : F,∑ d : F,(a c*star (a d))*
        ∑ E ∈ (sourceMaskSupport F c.val d.val).powerset,
          ∑ k ∈ BadFrequencySectors.boundedKeys H,∑ j : Fin (columnDyadicLength H+1),
            ∑ I ∈ NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j,
              offDiagonalKeep F c d*NaturalActualTail.packetTerm F hF c.val d.val
                QuadraticInitialBound.sieveCutoff L E
                (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
  unfold tupleNearOffDiagonalGram NaturalActualTail.nearPacket
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.mul_sum]
  have he := NaturalFrequencyReindex.cutoff_sum_by_sectors_dyads H hH
    (fun h => offDiagonalKeep F c d*NaturalActualTail.packetTerm F hF c.val d.val
      QuadraticInitialBound.sieveCutoff L E h)
  rw [offDiagonal_packetTerm_zero F hF hpF c d,zero_add] at he
  exact he

theorem actual_pair_reindex (F : Finset ColourTuple)
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (f : ColourTuple → ColourTuple → ℂ) :
    (∑ c : F,∑ d : F,f c.val d.val)=
      ∑ g ∈ actualTablePool F,∑ r ∈ residualFibre F g,
        f (recoverLeft g r.1) (recoverRight g r.2) := by
  calc
    _ = ∑ c ∈ F,∑ d ∈ F,f c d := by
      rw [Finset.sum_coe_sort F (fun c => ∑ d : F,f c d.val)]
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_coe_sort F (f c)
    _ = ∑ p ∈ F.product F,f p.1 p.2 :=
      (Finset.sum_product F F (fun p => f p.1 p.2)).symm
    _ = ∑ g ∈ actualTablePool F,∑ p ∈ pairFibre F g,f p.1 p.2 := pair_sum_by_table F _
    _ = _ := Finset.sum_congr rfl fun g hg => (sum_reindex F g hpF _).symm

theorem tupleNearOffDiagonalGram_eq_residual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (a : F → ℂ) (L H : ℝ) :
    tupleNearOffDiagonalGram F hF a L H=
      ∑ g ∈ actualTablePool F,∑ r ∈ residualFibre F g,
        if recoverLeft g r.1=recoverRight g r.2 then 0 else
          tupleCoefficientExtension F a (recoverLeft g r.1)*
            star (tupleCoefficientExtension F a (recoverRight g r.2))*
              NaturalActualTail.nearPacket F hF (recoverLeft g r.1) (recoverRight g r.2)
                QuadraticInitialBound.sieveCutoff L H := by
  rw [← actual_pair_reindex F hpF (fun c d => if c=d then 0 else
    tupleCoefficientExtension F a c*star (tupleCoefficientExtension F a d)*
      NaturalActualTail.nearPacket F hF c d QuadraticInitialBound.sieveCutoff L H)]
  unfold tupleNearOffDiagonalGram
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  simp only [tupleCoefficientExtension_apply,offDiagonalKeep,Subtype.ext_iff]
  split_ifs <;> simp

theorem residual_recovered_data (F : Finset ColourTuple)
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (r : ColourTuple × ColourTuple) (hr : r ∈ residualFibre F g) :
    recoverLeft g r.1 ∈ F ∧ recoverRight g r.2 ∈ F ∧
      table (recoverLeft g r.1) (recoverRight g r.2)=g := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have he := recover_pair_of_mem hpF hp
  have hl : recoverLeft g (residualPair p).1=p.1 := congrArg Prod.fst he
  have hh : recoverRight g (residualPair p).2=p.2 := congrArg Prod.snd he
  rw [hl,hh]
  obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hp
  exact ⟨hc,hd,ht⟩

theorem nearPacket_eq_sectors_of_ne (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F) (hne : c ≠ d)
    (L H : ℝ) (hH : 0 ≤ H) :
    NaturalActualTail.nearPacket F hF c d QuadraticInitialBound.sieveCutoff L H=
      ∑ E ∈ (tableSourceMask F (table c d)).powerset,
        ∑ k ∈ BadFrequencySectors.boundedKeys H,∑ j : Fin (columnDyadicLength H+1),
          ∑ I ∈ NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j,
            NaturalActualTail.packetTerm F hF c d QuadraticInitialBound.sieveCutoff L E
              (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
  unfold NaturalActualTail.nearPacket
  rw [sourceMaskSupport_eq_table F hF c d hc hd (hpF c hc) (hpF d hd)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [NaturalFrequencyReindex.cutoff_sum_by_sectors_dyads H hH]
  have hz := primitiveRow_zero_offdiagonal F hF c d hc hd (hpF c hc) (hpF d hd) hne
  simp only [NaturalActualTail.packetTerm,NaturalActualTail.packetCoefficient,hz,
    star_zero,mul_zero,zero_mul,zero_add]

theorem tupleNearOffDiagonalGram_eq_table_sectors (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (a : F → ℂ) (L H : ℝ) (hH : 0 ≤ H) :
    tupleNearOffDiagonalGram F hF a L H=
      ∑ g ∈ actualTablePool F,∑ E ∈ (tableSourceMask F g).powerset,
        ∑ k ∈ BadFrequencySectors.boundedKeys H,∑ j : Fin (columnDyadicLength H+1),
          ∑ r ∈ residualFibre F g,
            if recoverLeft g r.1=recoverRight g r.2 then 0 else
              tupleCoefficientExtension F a (recoverLeft g r.1)*
                star (tupleCoefficientExtension F a (recoverRight g r.2))*
                  ∑ I ∈ NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j,
                    NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2)
                      QuadraticInitialBound.sieveCutoff L E
                      (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
  rw [tupleNearOffDiagonalGram_eq_residual F hF hpF a L H]
  apply Finset.sum_congr rfl
  intro g hg
  calc
    _ = ∑ r ∈ residualFibre F g,∑ E ∈ (tableSourceMask F g).powerset,
        ∑ k ∈ BadFrequencySectors.boundedKeys H,∑ j : Fin (columnDyadicLength H+1),
          if recoverLeft g r.1=recoverRight g r.2 then 0 else
            tupleCoefficientExtension F a (recoverLeft g r.1)*
              star (tupleCoefficientExtension F a (recoverRight g r.2))*
                ∑ I ∈ NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j,
                  NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2)
                    QuadraticInitialBound.sieveCutoff L E
                    (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hdata := residual_recovered_data F hpF g r hr
      by_cases he : recoverLeft g r.1=recoverRight g r.2
      · simp only [he,ite_true,Finset.sum_const_zero]
      · rw [if_neg he,nearPacket_eq_sectors_of_ne F hF hpF _ _ hdata.1 hdata.2.1 he L H hH,
          hdata.2.2]
        simp only [he,ite_false,Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm

theorem recoverLeft_injective (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0) :
    Function.Injective (recoverLeft g) := by
  intro a b he
  funext j
  have hj := congrFun he j
  exact mul_left_cancel₀
    (Finset.prod_ne_zero_iff.mpr fun k _ => hgn j k) hj

theorem recoverRight_injective (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0) :
    Function.Injective (recoverRight g) := by
  intro a b he
  funext k
  have hk := congrFun he k
  exact mul_left_cancel₀
    (Finset.prod_ne_zero_iff.mpr fun j _ => hgn j k) hk

def leftOriginalUnitMask (g : SharedTable) (c : ColourTuple) : ℂ :=
  if c=recoverLeft g NaturalDiagonalMask.unitTuple then 1 else 0
def rightOriginalUnitMask (g : SharedTable) (c : ColourTuple) : ℂ :=
  if c=recoverRight g NaturalDiagonalMask.unitTuple then 1 else 0

theorem leftOriginalUnitMask_recover (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0)
    (a : ColourTuple) :
    leftOriginalUnitMask g (recoverLeft g a)=NaturalDiagonalMask.unitMask a := by
  simp only [leftOriginalUnitMask,NaturalDiagonalMask.unitMask,
    (recoverLeft_injective g hgn).eq_iff]

theorem rightOriginalUnitMask_recover (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0)
    (b : ColourTuple) :
    rightOriginalUnitMask g (recoverRight g b)=NaturalDiagonalMask.unitMask b := by
  simp only [rightOriginalUnitMask,NaturalDiagonalMask.unitMask,
    (recoverRight_injective g hgn).eq_iff]

theorem leftOriginalUnitMask_norm (g : SharedTable) (c : ColourTuple) :
    ‖leftOriginalUnitMask g c‖ ≤ 1 := by
  unfold leftOriginalUnitMask
  split_ifs <;> norm_num

theorem rightOriginalUnitMask_norm (g : SharedTable) (c : ColourTuple) :
    ‖rightOriginalUnitMask g c‖ ≤ 1 := by
  unfold rightOriginalUnitMask
  split_ifs <;> norm_num

def tableArrayEnergy (left : Bool) (F : Finset ColourTuple) (g : SharedTable)
    (a : ColourTuple → ℂ) : ℝ :=
  ∑ b ∈ arrayFamily left F g,‖a (arrayRecover left g b)‖^2

theorem tableArrayEnergy_nonneg (left : Bool) (F : Finset ColourTuple) (g : SharedTable)
    (a : ColourTuple → ℂ) : 0 ≤ tableArrayEnergy left F g a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem incidentArrayMass_one_dominates (left : Bool) (F : Finset ColourTuple)
    (g : SharedTable) (a : ColourTuple → ℂ)
    (hn : ∀ b ∈ arrayFamily left F g,(arrayRecover left g b) 0 ≠ 0) :
    ((idealDivisors (diagonalProduct g)).card:ℝ)*tableArrayEnergy left F g a ≤
      incidentArrayMass left F g {1} a (fun _ _ _ _ _ => 1) := by
  unfold tableArrayEnergy incidentArrayMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hcard : (1:ℝ) ≤ ((idealDivisors ((arrayRecover left g b) 0)).card:ℝ) := by
    have hone : (1:Ideal O) ∈ idealDivisors ((arrayRecover left g b) 0) :=
      (mem_idealDivisors (hn b hb)).mpr (one_dvd _)
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hone⟩
  simp only [Finset.sum_singleton,mul_one,Finset.sum_const,nsmul_eq_mul,
    Finset.card_singleton,Nat.cast_one,one_mul]
  have hh := mul_le_mul_of_nonneg_right hcard (sq_nonneg ‖a (arrayRecover left g b)‖)
  have hh' := mul_le_mul_of_nonneg_left hh
    (Nat.cast_nonneg (idealDivisors (diagonalProduct g)).card :
      (0:ℝ) ≤ ((idealDivisors (diagonalProduct g)).card:ℝ))
  simpa only [one_mul,mul_assoc] using hh'

theorem table_mask_root_cost (F : Finset ColourTuple) (g : SharedTable)
    (hgn : ∀ j k,g j k ≠ 0) (a : ColourTuple → ℂ)
    (hnL : ∀ b ∈ arrayFamily true F g,(arrayRecover true g b) 0 ≠ 0)
    (hnR : ∀ b ∈ arrayFamily false F g,(arrayRecover false g b) 0 ≠ 0) :
    ((tableSourceMask F g).powerset.card:ℝ)*
      Real.sqrt (tableArrayEnergy true F g a)*Real.sqrt (tableArrayEnergy false F g a) ≤
      4*Real.sqrt (incidentArrayMass true F g {1} a (fun _ _ _ _ _ => 1))*
        Real.sqrt (incidentArrayMass false F g {1} a (fun _ _ _ _ _ => 1)) := by
  let D : ℝ := ((idealDivisors (diagonalProduct g)).card:ℝ)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hL := incidentArrayMass_one_dominates true F g a hnL
  have hR := incidentArrayMass_one_dominates false F g a hnR
  have he : Real.sqrt (D*tableArrayEnergy true F g a)*
      Real.sqrt (D*tableArrayEnergy false F g a)=
      D*Real.sqrt (tableArrayEnergy true F g a)*Real.sqrt (tableArrayEnergy false F g a) := by
    rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
    have hh := Real.mul_self_sqrt hD
    calc
      _ = (Real.sqrt D*Real.sqrt D)*Real.sqrt (tableArrayEnergy true F g a)*
          Real.sqrt (tableArrayEnergy false F g a) := by ring
      _ = _ := by rw [hh]
  calc
    _ ≤ (4*D)*Real.sqrt (tableArrayEnergy true F g a)*Real.sqrt (tableArrayEnergy false F g a) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      dsimp [D]
      exact_mod_cast table_mask_card F g hgn
    _ = 4*(Real.sqrt (D*tableArrayEnergy true F g a)*
        Real.sqrt (D*tableArrayEnergy false F g a)) := by rw [he]; ring
    _ ≤ _ := by
      have hh := mul_le_mul (Real.sqrt_le_sqrt hL) (Real.sqrt_le_sqrt hR)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 4)

def tableSectorPacket (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (a : ColourTuple → ℂ) (L H : ℝ) (g : SharedTable)
    (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ)
    (j : Fin (columnDyadicLength H+1)) : ℂ :=
  ∑ r ∈ residualFibre F g,if recoverLeft g r.1=recoverRight g r.2 then 0 else
    a (recoverLeft g r.1)*star (a (recoverRight g r.2))*
      ∑ I ∈ NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j,
        NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2)
          QuadraticInitialBound.sieveCutoff L E
          (BadFrequencySectors.keyFactor k*primaryGenerator I)

theorem actualTablePool_valid (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hg : g ∈ actualTablePool F) :
    (∀ j k,g j k ≠ 0) ∧
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) := by
  obtain ⟨⟨c,d⟩,hp,rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hp
  exact ⟨fun j k => (table_admissible (hF c hc) j k).1,
    table_pairwise (hpF c hc) (hpF d hd)⟩

/-- Literal table, puncture and source-sector summation, relative to a
bound on EACH displayed finite packet. The analytic packet estimate is
an explicit intermediate input; this lemma only closes its actual mass
and counting interfaces. -/
theorem near_norm_of_table_sector_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple)
      (hF : ∀ c ∈ F,∀ j,Admissible (c j))
      (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
      (a : F → ℂ) (L H Y K : ℝ),0 ≤ H → 1 ≤ Y → 0 ≤ K →
      (∀ c ∈ F,(Ideal.absNorm (weightedIdeal c):ℝ) ≤ Y) →
      (∀ g ∈ actualTablePool F,∀ E ∈ (tableSourceMask F g).powerset,
        ∀ k ∈ BadFrequencySectors.boundedKeys H,∀ j : Fin (columnDyadicLength H+1),
          ‖tableSectorPacket F hF (tupleCoefficientExtension F a) L H g E k j‖ ≤
            K*Real.sqrt (tableArrayEnergy true F g (tupleCoefficientExtension F a))*
              Real.sqrt (tableArrayEnergy false F g (tupleCoefficientExtension F a))) →
      ‖tupleNearOffDiagonalGram F hF a L H‖ ≤
        K*C*(((BadFrequencySectors.boundedKeys H).card:ℝ)*(columnDyadicLength H+1:ℕ))*
          Y^ε*(∑ c : F,‖a c‖^2) := by
  obtain ⟨C₀,hC₀,hinc⟩ := packet_sum_actual_incidence ε hε {1}
  refine ⟨4*C₀,by positivity,?_⟩
  intro F hF hpF a L H Y K hH hY hK hheight hpacket
  let a₀ := tupleCoefficientExtension F a
  let Q : ℝ := ((BadFrequencySectors.boundedKeys H).card:ℝ)*(columnDyadicLength H+1:ℕ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let packet : SharedTable → ℂ := fun g => ∑ E ∈ (tableSourceMask F g).powerset,
    ∑ k ∈ BadFrequencySectors.boundedKeys H,∑ j : Fin (columnDyadicLength H+1),
      tableSectorPacket F hF a₀ L H g E k j
  have hpacket' : ∀ g ∈ actualTablePool F,‖packet g‖ ≤
      (4*K*Q)*Real.sqrt (incidentArrayMass true F g {1} a₀ (fun _ _ _ _ _ => 1))*
        Real.sqrt (incidentArrayMass false F g {1} a₀ (fun _ _ _ _ _ => 1)) := by
    intro g hg
    have hv := actualTablePool_valid F hF hpF g hg
    have hnL : ∀ b ∈ arrayFamily true F g,(arrayRecover true g b) 0 ≠ 0 := by
      intro b hb
      exact (hF _ (leftFamily_ok hF hpF hv.1 hv.2 hb).1 0).1
    have hnR : ∀ b ∈ arrayFamily false F g,(arrayRecover false g b) 0 ≠ 0 := by
      intro b hb
      exact (hF _ (rightFamily_ok hF hpF hv.1 hv.2 hb).1 0).1
    have hm := table_mask_root_cost F g hv.1 a₀ hnL hnR
    calc
      _ ≤ ∑ E ∈ (tableSourceMask F g).powerset,
          ∑ k ∈ BadFrequencySectors.boundedKeys H,∑ j : Fin (columnDyadicLength H+1),
            K*Real.sqrt (tableArrayEnergy true F g a₀)*Real.sqrt (tableArrayEnergy false F g a₀) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro E hE
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hpacket g hg E hE k hk j)
      _ = (K*Q)*(((tableSourceMask F g).powerset.card:ℝ)*
          Real.sqrt (tableArrayEnergy true F g a₀)*Real.sqrt (tableArrayEnergy false F g a₀)) := by
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
        dsimp [Q]
        ring
      _ ≤ (K*Q)*(4*Real.sqrt (incidentArrayMass true F g {1} a₀ (fun _ _ _ _ _ => 1))*
          Real.sqrt (incidentArrayMass false F g {1} a₀ (fun _ _ _ _ _ => 1))) :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg hK hQ)
      _ = _ := by ring
  have hsum := hinc F hF hpF (actualTablePool F) Y (4*K*Q) a₀
    (fun _ _ _ _ _ => 1) (fun _ _ _ _ _ => 1) packet hY (by positivity) hheight
    (by intros; norm_num) (by intros; norm_num) hpacket'
  have he : tupleNearOffDiagonalGram F hF a L H=∑ g ∈ actualTablePool F,packet g :=
    tupleNearOffDiagonalGram_eq_table_sectors F hF hpF a L H hH
  rw [he]
  apply hsum.trans_eq
  rw [tupleCoefficientExtension_mass]
  dsimp [Q]
  ring

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.source_norm_clip
#print axioms Qrh.JointDetector.NaturalSelectedNorm.table_mask_card
#print axioms Qrh.JointDetector.NaturalSelectedNorm.offDiagonal_packetTerm_zero
#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleNearOffDiagonalGram_eq_table_sectors
#print axioms Qrh.JointDetector.NaturalSelectedNorm.table_mask_root_cost
#print axioms Qrh.JointDetector.NaturalSelectedNorm.near_norm_of_table_sector_bound
