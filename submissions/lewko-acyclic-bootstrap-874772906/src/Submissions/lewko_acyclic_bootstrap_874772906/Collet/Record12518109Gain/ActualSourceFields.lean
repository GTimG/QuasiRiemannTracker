import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Upstream.ActualRowwiseMarkedInverse
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Upstream.ActualRowwiseMarkedPlain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Upstream.AnnularPool
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.NaturalEndpoint
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualFiberCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
/- Source-identical natural row data and actual fixed-mesh moment supplier
adapted from PR63 ActualMarkedGates, ActualWeightedCount and Target836
ActualWeightedFixedMesh; Apache-2.0. Only namespaces/imports are relocated. -/
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Record12518109GainActual
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem momentElement_injective : Function.Injective momentElement := by
  intro u v h
  exact Subtype.ext (congrArg (fun z : NonzeroElement=>z.val) h)

/-- Actual marked inverse energy pulled back to the sixth-power-free row
population used by the detector count. No inverse-moment premise remains. -/
theorem actual_free_inverse_energy (W : ℝ→ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hεm : 0<εm) (K : ℕ) :
    ∃degree : ℕ,∀data : RowData,∃C U₀ : ℝ,0<C ∧ 1<U₀ ∧
      ∀U : ℝ,U₀≤U → ∀{ι : Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
      ∀(L : ι→Finset (Ideal O))(ell : ι→ℝ),
      (∀s,0≤ell s) → (∀s,∀P∈L s,Prime P) →
      (∀s,∀P∈L s,((P.absNorm:ℝ)/U^(ell s))∈Icc (1:ℝ) 2) →
      (∀s,((deletedBase data).modulus.absNorm:ℝ)<U^(ell s)) →
      ∀(ηslot : Character)(ν : ι→Character)(σslot vslot : ι→ℝ)(choice : FreeRow→ℝ),
      (∀s,lo≤σslot s) → (∀s,σslot s≤hi) →
      ∀r : ℝ,0≤r → r+2*(∑s,ell s)<1 → 2*r+8*(∑s,ell s)<3 →
      ∀rows : Finset FreeRow,(∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀χ : FreeRow→Character,
      (∀u∈rows,∀I,idealCoeff (χ u) I=idealCoeff (data.character (momentElement u)) I) →
      ∀tstar : ℝ,∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,
      ∀height t : ℝ,0≤height → t∈Icc (-height) height →
      (∀u∈rows,|choice u|≤height) →
      (∑u∈rows,‖polynomial (χ u) true ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ t*
        (∏s,naturalSlot (naturalRow ηslot u.val u.property.1).character (L s)
          (fun I=>idealCoeff (ν s) I*HeckePrimeAnnular.annularWeight W (U^(ell s))
            (σslot s) (choice u+vslot s) I) (U^(ell s)))‖^2)≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,hfield⟩ := Record12518109GainDeletion.annular_rowwise_inverse_marked_energy W lo hi εm hWs hW hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,hfield⟩ := hfield data
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell hell hprime hratio hlarge ηslot ν σslot vslot choice hσlo hσhi
    r hr hcap1 hcap2 rows hrows χ hcoeff tstar n hn σ hσ height t hh ht hchoice
  let choice' : NonzeroElement→ℝ := Function.extend momentElement choice (fun _=>0)
  have hchoice' (u : FreeRow) : choice' (momentElement u)=choice u :=
    momentElement_injective.extend_apply choice (fun _=>0) u
  have hnorm (u : NonzeroElement) (hu : u∈rows.image momentElement) : ‖eisEmbedding u.val‖^2≤U := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact hrows v hv
  have hheight (u : NonzeroElement) (hu : u∈rows.image momentElement) : |choice' u|≤height := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    rw [hchoice']
    exact hchoice v hv
  have he := hfield U hU hK L ell hell hprime hratio hlarge ηslot ν σslot vslot choice'
    hσlo hσhi r hr hcap1 hcap2 (rows.image momentElement) hnorm tstar false n hn σ hσ
    height t hh ht hheight
  rw [Finset.sum_image (fun u _ v _ huv=>momentElement_injective huv)] at he
  simp only [orientedProfile,Bool.false_eq_true,ite_false,hchoice'] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [polynomial_eq_of_idealCoeff (χ u) (data.character (momentElement u)) (hcoeff u hu)]
  rfl

/-- Literal finite source data. The two representations identify the same
amplitude with the annular inverse pool and the canonical plain source pool;
no moment estimate is included among the fields. -/
structure NaturalBatch (base anchor : Label→Character) (bad : Label→Ideal O)
    (W : ℝ→ℂ) (lo hi U : ℝ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  slots : Finset Slot
  widths : Slot→ℝ
  sigma : Slot→ℝ
  relativeHeight : Slot→ℝ
  commonHeight : FreeRow→ℝ
  Q : FreeRow→Slot→ℂ
  rays : Label→Slot→RayQuotient.Characters M H
  inversePools : Slot→Finset (Ideal O)
  inverseBase : Character
  inverseCoefficients : Slot→Character
  widthsPositive : ∀s∈slots,0<widths s
  sigmaLower : ∀s∈slots,lo≤ sigma s
  sigmaUpper : ∀s∈slots,sigma s≤hi
  rowNorm : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U
  embeddingNorm : ∀u∈rows,‖eisEmbedding u.val‖^2≤U
  idealCoefficients : ∀u∈rows,∀j I,idealCoeff (family u j) I=
    idealCoeff ((momentData (base j)).character (momentElement u)) I
  elementCoefficients : ∀u∈rows,∀j n,elementCoeff (family u j) n=
    rowTwist (HeckeRowClosure.elementHom (base j))
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (1*u.val) n
  retained : ∀u∈rows,∀j,initialKeep (base j) (internalQ (bad j) (anchor j)) u.val
  inversePrime : ∀s∈slots,∀P∈inversePools s,Prime P
  inverseRatios : ∀s∈slots,∀P∈inversePools s,((P.absNorm:ℝ)/U^(widths s))∈Icc (1:ℝ) 2
  inverseLarge : ∀s∈slots,∀j,((deletedBase (momentData (base j))).modulus.absNorm:ℝ)<U^(widths s)
  inverseIdentity : ∀u∈rows,∀s∈slots,Q u s=
    naturalSlot (naturalRow inverseBase u.val u.property.1).character (inversePools s)
      (fun I=>idealCoeff (inverseCoefficients s) I*HeckePrimeAnnular.annularWeight W (U^(widths s))
        (sigma s) (commonHeight u+relativeHeight s) I) (U^(widths s))
  plainIdentity : ∀u∈rows,∀j,∀s∈slots,Q u s=
    naturalSlot (family u j) (primePool M H 2 (U^(widths s)))
      (fun I=>idealCoeff (relativeCharacter M H hH (anchor j) (rays j s)) I*
        HeckePrimeAnnular.annularWeight W (U^(widths s)) (sigma s)
          (commonHeight u+relativeHeight s) I) (U^(widths s))

theorem actual_marked_source_fields_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (lo hi bΦ κ εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hκ : (3/4:ℝ)≤κ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκβ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      (∀s∈B.slots,B.widths s≤Cycle61MarkedPlain.markedPlainMesh κ εm) →
      ∀height : ℝ,0≤height → (∀s∈B.slots,|B.relativeHeight s|≤height) →
      (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀rows : Finset FreeRow,rows⊆B.rows → ∀label : Label,
      ∀selected : Finset Slot,selected⊆B.slots →
      (∀r : ℝ,0≤r → r+2*(∑s∈selected,B.widths s)<1 →
        2*r+8*(∑s∈selected,B.widths s)<3 →
        ∀tstar : ℝ,∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
          (U^r) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm)) ∧
      (∀m : ℝ,0≤ m → m≤1 → 2*m+6*κ*(∑s∈selected,B.widths s)≤1 →
        ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σ freq*
          polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σ freq*
            (∏s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm)) := by
  obtain ⟨Ji,hI⟩ := actual_free_inverse_energy W lo hi εm hWs hW hεm (Fintype.card Slot)
  choose Ci Ui hCi hUi hI using fun j=>hI (momentData (base j))
  have hP (j : Label) := Cycle61MarkedPlain.actual_rowwise_marked_plain_energy_fixedmesh (α:=Slot)
    M H hH W 1 2 bΦ lo hi κ εm (by norm_num) hWs hW (by norm_num) hbΦ hrad hκ hεm hβ hκβ
    (base j) (anchor j) (bad j) (hbadM j) (hbad0 j) (hbadTop j) (hbad72 j)
  choose Jp Cp hCp hP using hP
  let J := Ji+∑j,Jp j
  let C := 1+(∑j,Ci j)+(∑j,Cp j)
  let U₀ := 1+∑j,Ui j
  have hCis : 0≤∑j,Ci j := Finset.sum_nonneg (fun j _=>(hCi j).le)
  have hCps : 0≤∑j,Cp j := Finset.sum_nonneg (fun j _=>(hCp j).le)
  have hC : 0<C := by dsimp [C]; linarith
  have hUj (j : Label) : Ui j≤U₀ := by
    have hh := Finset.single_le_sum (fun k _=>(zero_lt_one.trans (hUi k)).le) (Finset.mem_univ j)
    dsimp [U₀]; linarith
  have hCij (j : Label) : Ci j≤C := by
    have hh := Finset.single_le_sum (fun k _=>(hCi k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  have hCpj (j : Label) : Cp j≤C := by
    have hh := Finset.single_le_sum (fun k _=>(hCp k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  have hJp (j : Label) : Jp j≤J := by
    have hh := Finset.single_le_sum (fun k _=>Nat.zero_le (Jp k)) (Finset.mem_univ j)
    dsimp [J]; omega
  have hPall : ∀ᶠ U : ℝ in atTop,∀j,_ := eventually_all.mpr hP
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hPall,eventually_ge_atTop U₀,eventually_gt_atTop (1:ℝ)] with U hPall hU₀ hU
  refine ⟨hU,?_⟩
  intro B hwm height hh hv hchoice rows hrows label selected hselected
  have hpow (k : ℕ)(hk : k≤J) : (1+height)^k≤(1+height)^J :=
    pow_le_pow_right₀ (by linarith) hk
  have hIC : Ci label*(1+height)^Ji≤C*(1+height)^J :=
    mul_le_mul (hCij label) (hpow Ji (by dsimp [J]; omega)) (by positivity) hC.le
  have hPC : Cp label*(1+height)^(Jp label)≤C*(1+height)^J :=
    mul_le_mul (hCpj label) (hpow _ (hJp label)) (by positivity) hC.le
  constructor
  · intro r hr hcap1 hcap2 tstar n hn σ hσ freq hfreq
    have he := hI label U ((hUj label).trans hU₀)
      (show Fintype.card selected≤Fintype.card Slot by simpa using Finset.card_le_univ selected)
      (fun s:selected=>B.inversePools s.val) (fun s=>B.widths s.val)
      (fun s=>(B.widthsPositive s.val (hselected s.property)).le)
      (fun s=>B.inversePrime s.val (hselected s.property))
      (fun s=>B.inverseRatios s.val (hselected s.property))
      (fun s=>B.inverseLarge s.val (hselected s.property) label)
      B.inverseBase (fun s=>B.inverseCoefficients s.val) (fun s=>B.sigma s.val)
      (fun s=>B.relativeHeight s.val) B.commonHeight
      (fun s=>B.sigmaLower s.val (hselected s.property))
      (fun s=>B.sigmaUpper s.val (hselected s.property)) r hr
      (by simpa only [Finset.sum_coe_sort] using hcap1)
      (by simpa only [Finset.sum_coe_sort] using hcap2)
      rows (fun u hu=>B.embeddingNorm u (hrows hu)) (fun u=>B.family u label)
      (fun u hu=>B.idealCoefficients u (hrows hu) label) tstar n hn σ hσ height freq hh hfreq
      (fun u hu=>hchoice u (hrows hu))
    have heq : (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
        (U^r) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(Ci label*(1+height)^Ji)*U^(1+εm) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 3
      rw [←Finset.prod_coe_sort selected (B.Q u)]
      exact Finset.prod_congr rfl (fun s _=>B.inverseIdentity u (hrows hu) s.val (hselected s.property))
    exact heq.trans (mul_le_mul_of_nonneg_right hIC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))
  · intro m hm hm1 hcap j k hjk σ hσ freq hfreq
    have hinj : Function.Injective (fun u:FreeRow=>u.val) := Subtype.val_injective
    have he := (hPall label).2 rows (fun u:FreeRow=>u.val) hinj (fun u=>B.family u label)
      (fun u hu=>B.elementCoefficients u (hrows hu) label)
      (fun u hu=>B.retained u (hrows hu) label) (fun u hu=>B.embeddingNorm u (hrows hu))
      m hm hm1 selected (fun s=>B.rays label s.val) (fun s=>B.widths s.val)
      (fun s=>B.sigma s.val) (fun s=>B.relativeHeight s.val) height B.commonHeight
      (fun s=>(B.widthsPositive s.val (hselected s.property)).le)
      (fun s=>hwm s.val (hselected s.property))
      (fun s=>B.sigmaLower s.val (hselected s.property))
      (fun s=>B.sigmaUpper s.val (hselected s.property)) hh
      (fun s=>hv s.val (hselected s.property)) (fun u hu=>hchoice u (hrows hu))
      (by simpa only [Finset.sum_coe_sort] using hcap) j k hjk σ hσ freq (abs_le.mpr hfreq)
    have heq : (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular)
        (U^m) σ freq*polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular)
        (U^m) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(Cp label*(1+height)^(Jp label))*U^(1+εm) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 3
      rw [←Finset.prod_coe_sort selected (B.Q u)]
      exact Finset.prod_congr rfl (fun s _=>B.plainIdentity u (hrows hu) label s.val (hselected s.property))
    exact heq.trans (mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))


end OAI.SevenEighths.Record12518109GainActual
end
