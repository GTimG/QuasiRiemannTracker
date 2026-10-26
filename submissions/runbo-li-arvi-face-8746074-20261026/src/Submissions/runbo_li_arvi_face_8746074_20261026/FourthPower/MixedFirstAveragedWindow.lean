/- Copyright (c) 2026 Sil. Apache-2.0.
The actual selected-divisor average, kept inside the first Fourier rows.
This is an exact source adapter and fourth-power transfer, not a new
moment estimate. Both windowed output energies remain literal quantities.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstLiveEnergy
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Cauchy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstAveragedWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge FourierBridge
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentCauchy CenteredMomentFirstAmplificationChoice
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalSecondZero MixedCommonRestriction MixedCommonAllocation MixedCommonCoefficient
open MixedLiteralAllocation MixedHeightEnergy MixedPoissonCompletion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Fifth-freeness is proved for the actual weighted column. The ordinary
restriction, distinct marked primes and their coprimality are all used. -/
theorem source_fifth_free (s : Source ι a b) (ha : 0<a) (seed I : Id)
    (hne : sourceCoefficient s ha seed I≠0) : SexticSieve.PowerFree 5 I := by
  obtain ⟨v,hv,hvne,hvI⟩ := finiteColumnCoefficient_witness
    (Fintype.piFinset (tuplePools s)) (originalTuple s ha seed) I hne
  have hweight : tupleWeight (punctureProduct s.S s.H) v≠0 :=
    (mul_ne_zero_iff.mp hvne).1
  have hr : tupleRestriction (punctureProduct s.S s.H) v := by
    by_contra hn
    exact hweight (by simp only [tupleWeight,if_neg hn])
  have hmem (j : ι⊕Fin 2) : v j∈tuplePools s j := (Fintype.mem_piFinset.mp hv) j
  have hzero (j : ι⊕Fin 2) : v j≠0 :=
    source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂ j _ (hmem j)
  let slot : ι→QRH.Record1252270103KernelMass.PrimeIdeal :=
    fun i=>⟨v (Sum.inl i),s.hp i _ (hmem (Sum.inl i))⟩
  have hinj : Function.Injective slot := by
    intro i j hij
    exact hr.2 (congrArg Subtype.val hij)
  have havoid (i : ι) : ¬(slot i).val∣v (Sum.inr 0)*v (Sum.inr 1) := by
    have hc : IsCoprime (slotProduct v) (v (Sum.inr 0)*v (Sum.inr 1)) :=
      (IsCoprime.mul_left_iff.mp hr.1.2).2
    have hd : (slot i).val∣slotProduct v := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hc' := hc.of_isCoprime_of_dvd_left hd
    intro hp
    exact (slot i).property.not_isUnit (hc'.isUnit_of_dvd' dvd_rfl hp)
  have hf := KernelWholeColumns.restricted_whole_fifth_free slot hinj
    (hzero (Sum.inr 0)) (hzero (Sum.inr 1)) hr.1.1 havoid
  have he : finiteTupleProduct v=
      v (Sum.inr 0)*v (Sum.inr 1)*KernelWholeColumns.markedProduct slot := by
    simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,
      KernelWholeColumns.markedProduct,slot]
    ring
  rw [←he,hvI] at hf
  exact hf

theorem residual_fifth_free (s : Source ι a b) (ha : 0<a)
    (seed G D I : Id) (hne : originalResidual s ha seed G D I≠0) :
    SexticSieve.PowerFree 5 I := by
  have hsource : sourceCoefficient s ha seed (G*I)≠0 := by
    intro hz
    exact hne (by simp only [originalResidual,hz,ite_self])
  have hf := source_fifth_free s ha seed (G*I) hsource
  intro P hP hp
  exact hf P hP (hp.trans (dvd_mul_left I G))

abbrev Columns (s : Source ι a b) (C G : Id) (hG : G≠0) :=
  CenteredMomentFirstPhysicalSource.columns C G hG (sourceColumns s)

def base (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (I : Columns s C G hG) : ℂ :=
  originalResidual s ha seed G D I*heightCoeff τ t I

def windowFactor (right : Bool) (V : ℝ→ℂ) (x θ : ℝ) : ℂ :=
  if right then star (columnPhase V x θ) else columnPhase V x θ

def selectedRow (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (right : Bool) (V : ℝ→ℂ) (X θ : ℝ) (F : Id) (z : O) : ℂ :=
  ∑I : Columns s C G hG,
    base s ha C G seed D hG τ t I*
      windowFactor right V (Real.log ((I.val.absNorm:ℝ)/X)) θ*
      (idealRowHom (primaryGenerator F) I.val)^2*
      gaussRow (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s) I)
        (CenteredMomentFirstPhysicalSource.element_supported C G hG (sourceColumns s) I) z

/-- The normalized output is the literal K4 ball energy. In the left
case the window is ordinary; in the right it is conjugated. -/
def outputEnergy (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (right : Bool) (V : ℝ→ℂ) (X θ K W : ℝ) : ℝ :=
  (gaussEnergy Finset.univ
    (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s))
    (CenteredMomentFirstPhysicalSource.element_supported C G hG (sourceColumns s))
    (fun I : Columns s C G hG=>base s ha C G seed D hG τ t I*
      windowFactor right V (Real.log ((I.val.absNorm:ℝ)/X)) θ)
    ballProfile (16*K*W^4)).re/W

/-- No fifth-free or analytic energy premise: the source supplies the
former, while the entire windowed output energy stays on the RHS. -/
theorem actual_selected_window_average (ε : ℝ) (hε : 0<ε) :
    ∃C0 : ℝ,0<C0 ∧ ∀s : Source ι a b,∀ha : 0<a,
    ∀(C G seed D : Id)(hG : G≠0)(τ : Character)(t : ℝ),
    ∀(right : Bool)(V : ℝ→ℂ)(X θ : ℝ),
    ∀(Ds : Finset Id)(rows : Finset O),
      (∀F∈Ds,Supported F)→(∀z∈rows,z≠0)→
    ∀(w : Id→ℝ)(W K L : ℝ),0<W→0<K→0≤L→
      (∀F∈Ds,0≤w F∧w F≤L)→(∀F∈Ds,(F.absNorm:ℝ)≤2*W)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤K)→
    (∑F∈Ds,w F*∑z∈rows,‖selectedRow s ha C G seed D hG τ t right V X θ F z‖^2)/W≤
      L*C0*(16*K*W^4)^ε*outputEnergy s ha C G seed D hG τ t right V X θ K W := by
  obtain ⟨C0,hC0,hbound⟩ := smoothed_weighted_average ε hε
  refine ⟨C0,hC0,?_⟩
  intro s ha C G seed D hG τ t right V X θ Ds rows hDs hrows w W K L hW hK hL hw hFN hzN
  have hf (I : Columns s C G hG) (_hI : I∈(Finset.univ : Finset (Columns s C G hG)))
      (hne : base s ha C G seed D hG τ t I*
        windowFactor right V (Real.log ((I.val.absNorm:ℝ)/X)) θ≠0) :
      GaussTransfer.FifthFree (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s) I) := by
    apply KernelWholeColumns.element_fifth_free
    rw [CenteredMomentFirstPhysicalSource.element_span]
    exact residual_fifth_free s ha seed G D I
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  have hh := hbound Ds rows hDs hrows w (fun _ _=>1) W K L hW hK hL hw
    (fun _ _ _ _=>⟨zero_le_one,le_rfl⟩) hFN hzN Finset.univ
    (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s))
    (CenteredMomentFirstPhysicalSource.element_supported C G hG (sourceColumns s))
    (fun I : Columns s C G hG=>base s ha C G seed D hG τ t I*
      windowFactor right V (Real.log ((I.val.absNorm:ℝ)/X)) θ) hf
  simp only [one_mul,CenteredMomentFirstPhysicalSource.element_span] at hh
  exact hh.trans_eq (by unfold outputEnergy;ring)

/-- The Fourier engine's row index is (selected divisor, physical row).
The real square root is inserted BEFORE Cauchy; no D-dependent column
vector is substituted for the common base coefficient. -/
def rowVector (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (reflect : Bool)
    (p : Id×O) (I : Columns s C G hG) : ℂ :=
  (Real.sqrt (w p.1/W):ℂ)*base s ha C G seed D hG τ t I*
    (idealRowHom (primaryGenerator p.1) I.val)^2*
    gaussRow (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s) I)
      (CenteredMomentFirstPhysicalSource.element_supported C G hG (sourceColumns s) I)
      (if reflect then -p.2 else p.2)

theorem left_column (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (V : ℝ→ℂ) (X θ : ℝ) (p : Id×O) :
    leftColumn Finset.univ (rowVector s ha C G seed D hG τ t w W false p) V
      (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X)) θ=
    (Real.sqrt (w p.1/W):ℂ)*selectedRow s ha C G seed D hG τ t false V X θ p.1 p.2 := by
  simp only [leftColumn,rowVector,selectedRow,windowFactor,Bool.false_eq_true,
    if_false,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem right_column (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (V : ℝ→ℂ) (X θ : ℝ) (p : Id×O) :
    rightColumn Finset.univ (rowVector s ha C G seed D hG τ t w W true p) V
      (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X)) θ=
    (Real.sqrt (w p.1/W):ℂ)*star (selectedRow s ha C G seed D hG τ t true V X θ p.1 (-p.2)) := by
  simp only [rightColumn,rowVector,selectedRow,windowFactor,if_true,
    star_sum,star_mul,star_star,Finset.mul_sum,Complex.star_def,map_mul,map_pow,
    Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [←Complex.star_def,star_star]
  ring

private theorem root_norm_sq (r : ℝ) (hr : 0≤r) (z : ℂ) :
    ‖(Real.sqrt r:ℂ)*z‖^2=r*‖z‖^2 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow,Real.sq_sqrt hr]

theorem left_column_energy (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (hW : 0<W)
    (Ds : Finset Id) (rows : Finset O) (hw : ∀F∈Ds,0≤w F)
    (V : ℝ→ℂ) (X θ : ℝ) :
    (∑p∈Ds×ˢrows,‖leftColumn Finset.univ
      (rowVector s ha C G seed D hG τ t w W false p) V
        (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X)) θ‖^2)=
      (∑F∈Ds,w F*∑z∈rows,‖selectedRow s ha C G seed D hG τ t false V X θ F z‖^2)/W := by
  rw [Finset.sum_product,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro F hF
  simp_rw [left_column,root_norm_sq (w F/W) (div_nonneg (hw F hF) hW.le)]
  rw [←Finset.mul_sum]
  ring

theorem right_column_energy (s : Source ι a b) (ha : 0<a) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (hW : 0<W)
    (Ds : Finset Id) (rows : Finset O) (hw : ∀F∈Ds,0≤w F)
    (V : ℝ→ℂ) (X θ : ℝ) :
    (∑p∈Ds×ˢrows,‖rightColumn Finset.univ
      (rowVector s ha C G seed D hG τ t w W true p) V
        (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X)) θ‖^2)=
      (∑F∈Ds,w F*∑z∈rows.image Neg.neg,
        ‖selectedRow s ha C G seed D hG τ t true V X θ F z‖^2)/W := by
  rw [Finset.sum_product,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.sum_image (fun x _ y _ h=>neg_injective h)]
  simp_rw [right_column,root_norm_sq (w F/W) (div_nonneg (hw F hF) hW.le),norm_star]
  rw [←Finset.mul_sum]
  ring

/-- Both actual averaged Fourier row energies. The two child radii may
be different; the right branch is reflected before applying pushforward.
The weighted common source and every literal prefix/seed remain fixed. -/
theorem paired_fourier_row_transfer (ε : ℝ) (hε : 0<ε) :
    ∃C0 : ℝ,0<C0 ∧ ∀s : Source ι a b,∀ha : 0<a,
    ∀(C G seed D : Id)(hC : C≠0)(hG : G≠0)(τ₁ τ₂ : Character)(t₁ t₂ : ℝ),
    ∀(Ds : Finset Id)(rows : Finset O),
      (∀F∈Ds,Supported F)→(∀z∈rows,z≠0)→
    ∀(w : Id→ℝ)(W KL KR L : ℝ),0<W→0<KL→0<KR→0≤L→
      (∀F∈Ds,0≤w F∧w F≤L)→(∀F∈Ds,(F.absNorm:ℝ)≤2*W)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤KL)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤KR)→
    ∀(V₁ V₂ : ℝ→ℂ)(X₁ X₂ θ : ℝ),
    Real.sqrt (∑p∈Ds×ˢrows,‖leftColumn Finset.univ
      (rowVector s ha G C seed D hC τ₁ t₁ w W false p) V₁
        (fun I : Columns s G C hC=>Real.log ((I.val.absNorm:ℝ)/X₁)) θ‖^2)*
    Real.sqrt (∑p∈Ds×ˢrows,‖rightColumn Finset.univ
      (rowVector s ha C G seed D hG τ₂ t₂ w W true p) V₂
        (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X₂)) θ‖^2)≤
    Real.sqrt (L*C0*(16*KL*W^4)^ε*outputEnergy s ha G C seed D hC τ₁ t₁ false V₁ X₁ θ KL W)*
    Real.sqrt (L*C0*(16*KR*W^4)^ε*outputEnergy s ha C G seed D hG τ₂ t₂ true V₂ X₂ θ KR W) := by
  obtain ⟨C0,hC0,hbound⟩ := actual_selected_window_average (ι:=ι) (a:=a) (b:=b) ε hε
  refine ⟨C0,hC0,?_⟩
  intro s ha C G seed D hC hG τ₁ τ₂ t₁ t₂ Ds rows hDs hrows w W KL KR L hW hKL hKR hL hw hFN hKLrows hKRrows V₁ V₂ X₁ X₂ θ
  have hleft := hbound s ha G C seed D hC τ₁ t₁ false V₁ X₁ θ Ds rows hDs hrows
    w W KL L hW hKL hL hw hFN hKLrows
  have hright := hbound s ha C G seed D hG τ₂ t₂ true V₂ X₂ θ Ds (rows.image Neg.neg) hDs
    (by intro z hz;obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hz;exact neg_ne_zero.mpr (hrows k hk))
    w W KR L hW hKR hL hw hFN
    (by intro z hz;obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hz
        simpa only [Ideal.span_singleton_neg] using hKRrows k hk)
  rw [left_column_energy s ha G C seed D hC τ₁ t₁ w W hW Ds rows (fun F hF=>(hw F hF).1),
    right_column_energy s ha C G seed D hG τ₂ t₂ w W hW Ds rows (fun F hF=>(hw F hF).1)]
  exact mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- One Fourier density is chosen before the source, the selected set,
its weights and both common columns. The selected-divisor average is
inside the same integral. In particular the right Gauss row is at -z
and has the conjugated column window, exactly as above. -/
theorem actual_whole_pair_separation (Wprofile : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ)
    (M : Fin 4→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0→|y|≤M i) (A J : ℕ) :
    ∃C0 : ℝ,0≤C0 ∧ ∀R : ℝ,0<R→∃density : 𝓢(ℝ,ℂ),
      (∀s : Source ι a b,∀ha : 0<a,
        ∀(C G seed D : Id)(hC : C≠0)(hG : G≠0)(τ₁ τ₂ : Character)(t₁ t₂ : ℝ),
        ∀(Ds : Finset Id)(rows : Finset O)(w : Id→ℝ)(W : ℝ),0<W→
          (∀F∈Ds,0≤w F)→∀(ρ x : Id×O→ℝ)(η : Id×O→ℂ)(X₁ X₂ : ℝ),
        (∑p∈Ds×ˢrows,η p*
          ∑i : Columns s G C hC,∑j : Columns s C G hG,
            (rowVector s ha G C seed D hC τ₁ t₁ w W false p i*
              star (rowVector s ha C G seed D hG τ₂ t₂ w W true p j))*
            wholeKernel Wprofile V R (ρ p) (x p)
              (Real.log ((i.val.absNorm:ℝ)/X₁)) (Real.log ((j.val.absNorm:ℝ)/X₂)))=
        ∫θ : ℝ,∑p∈Ds×ˢrows,((w p.1/W:ℝ):ℂ)*η p*
          rowPhase V (ρ p) (x p) θ*
          selectedRow s ha G C seed D hC τ₁ t₁ false (V 2) X₁ θ p.1 p.2*
          star (selectedRow s ha C G seed D hG τ₂ t₂ true (V 3) X₂ θ p.1 (-p.2))*
          density θ) ∧
      Integrable (fun θ : ℝ=>(1+‖θ‖)^J*‖density θ‖) ∧
      (1+R)^A*(∫θ : ℝ,(1+‖θ‖)^J*‖density θ‖)≤C0 ∧
      (∀θ : ℝ,(1+R)^A*(1+‖θ‖)^J*‖density θ‖≤C0) := by
  obtain ⟨C0,hC0,hsep⟩ := whole_product_pair_separation Wprofile V M hM hV A J
  refine ⟨C0,hC0,?_⟩
  intro R hR
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep R hR
  refine ⟨density,?_,hi,hm,hp⟩
  intro s ha C G seed D hC hG τ₁ τ₂ t₁ t₂ Ds rows w W hW hw ρ x η X₁ X₂
  let c := rowVector s ha G C seed D hC τ₁ t₁ w W false
  let d := rowVector s ha C G seed D hG τ₂ t₂ w W true
  let u := fun i : Columns s G C hC=>Real.log ((i.val.absNorm:ℝ)/X₁)
  let v := fun j : Columns s C G hG=>Real.log ((j.val.absNorm:ℝ)/X₂)
  have he (p : Id×O) := hid Finset.univ Finset.univ (c p) (d p) u v (ρ p) (x p)
  change (∑p∈Ds×ˢrows,η p*
    ∑i : Columns s G C hC,∑j : Columns s C G hG,
      (c p i*star (d p j))*wholeKernel Wprofile V R (ρ p) (x p) (u i) (v j))=_
  simp_rw [he]
  change (∑p∈Ds×ˢrows,η p*∫θ : ℝ,rowPhase V (ρ p) (x p) θ*
    leftColumn Finset.univ (c p) (V 2) u θ*
    rightColumn Finset.univ (d p) (V 3) v θ*density θ)=_
  calc
    _ = ∫θ : ℝ,∑p∈Ds×ˢrows,η p*(rowPhase V (ρ p) (x p) θ*
        leftColumn Finset.univ (c p) (V 2) u θ*
        rightColumn Finset.univ (d p) (V 3) v θ*density θ) := by
      rw [integral_finsetSum _ (fun p _=>paired_columns_integrable density V (ρ p) (x p)
        Finset.univ Finset.univ (c p) (d p) u v (η p))]
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with θ
      apply Finset.sum_congr rfl
      intro p hp
      have hwP : 0≤w p.1/W := div_nonneg (hw p.1 (Finset.mem_product.mp hp).1) hW.le
      have hs : (Real.sqrt (w p.1/W):ℂ)^2=((w p.1/W:ℝ):ℂ) := by
        norm_cast
        exact Real.sq_sqrt hwP
      dsimp only [c,d,u,v]
      rw [left_column,right_column]
      linear_combination (norm := ring_nf) η p*rowPhase V (ρ p) (x p) θ*
        selectedRow s ha G C seed D hC τ₁ t₁ false (V 2) X₁ θ p.1 p.2*
        star (selectedRow s ha C G seed D hG τ₂ t₂ true (V 3) X₂ θ p.1 (-p.2))*
        density θ*hs

end
end Candidate.FourthPower.MixedFirstAveragedWindow
