/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B003
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentFiberGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPhysicalRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeletedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiberEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePaddedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePrimeGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceShift
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentDetectorMomentPrimeGeometry; sha256 8a67369f763c980eb7a060c9134f296913f0e47647f08df4dd73e58a09e9f9b5 -/
section
                                                                       
                                  
                                                                    
                                                                 
                                                           
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle25ProbeHighRowFamily
open ProbeHighRowFamily Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem weighted_sourceMoment_physical_scale (Z d ell : ℝ) (hZ : 0 ≤ Z) (hd : d≠0) :
    (Z^d)^(ell/d)=Z^ell := by
  rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]

theorem weighted_sourceMoment_separation_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hinj : Function.Injective ell) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ ∀d : ℝ,0<d→∀s t : Slot,s≠t→
      2*(Z^d)^(ell s/d)<1*(Z^d)^(ell t/d) ∨
      2*(Z^d)^(ell t/d)<1*(Z^d)^(ell s/d) := by
  have hs : ∀ᶠ Z : ℝ in atTop,∀s t : Slot,s≠t→
      2*Z^(ell s)<1*Z^(ell t) ∨ 2*Z^(ell t)<1*Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro s
    apply Filter.eventually_all.mpr
    intro t
    by_cases he : s=t
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h he))
    rcases lt_or_gt_of_ne (fun h=>he (hinj h)) with hlt|hlt
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell s) (ell t)
        (by norm_num) hlt] with Z hZ _
      exact Or.inl hZ
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell t) (ell s)
        (by norm_num) hlt] with Z hZ _
      exact Or.inr hZ
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with Z hs hZ
  refine ⟨hZ,?_⟩
  intro d hd s t hst
  simp only [weighted_sourceMoment_physical_scale Z d _ (by linarith) hd.ne']
  exact hs s t hst

theorem weighted_sourceMoment_fixedBase_norm_one (data : RowData) (P : Ideal O) (hP : Prime P)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    ‖fixedBase data.η data.m data.f P‖=1 := by
  rw [←baseCharacter_coeff]
  exact PrincipalSignalComparison.idealCoeff_norm_one_of_coprime
    (baseCharacter data) P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hlarge)

theorem weighted_sourceMoment_primeProfile_norm {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re ≤ 1)
    (P : Ideal O) : ‖primeProfile F.W X ζ P‖ ≤ 1 := by
  by_cases hw : F.W ((P.absNorm:ℝ)/X)=0
  · simp [primeProfile,hw]
  have hx := F.complex_support hw
  have hp : 0<(P.absNorm:ℝ)/X := lt_of_lt_of_le (by norm_num) hx.1
  have hnorm : ‖F.W ((P.absNorm:ℝ)/X)‖ ≤ 1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded _).1]
    exact (F.bounded _).2
  rw [primeProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : ((P.absNorm:ℝ)/X)^((ζ-1).re) ≤ 1 :=
    (Real.rpow_le_rpow_of_exponent_le hx.1
      (show (ζ-1).re ≤ 0 by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
        (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hnorm hr (Real.rpow_nonneg hp.le _) (by norm_num : (0:ℝ) ≤ 1)

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem weighted_sourceMoment_live_disjoint {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0<U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem weighted_sourceMoment_live_denominator {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0<U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact weighted_sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem weighted_sourceMoment_live_quotient_norm {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0<U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖ ≤ 1 := by
  rw [norm_div,norm_star,weighted_sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one₀ (fun s _=>norm_nonneg _)
    (fun s _=>weighted_sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

theorem weighted_sourceMoment_capacity_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hell : ∀s,0 ≤ ell s) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧ ∀d : ℝ,1/200 ≤ d→
      (∀s,1 ≤ 2*(Z^d)^(ell s/d)) ∧ ∀selected : Finset Slot,
      (∏s:selected,2*(Z^d)^(ell s/d)) ≤ 
        (Z^d)^((∑s:selected,ell s/d)+ε) := by
  have ht := (tendsto_rpow_atTop (show 0<ε/200 by positivity)).eventually
    (eventually_ge_atTop ((2:ℝ)^Fintype.card Slot))
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with Z ht hZ
  refine ⟨hZ,?_⟩
  intro d hd
  have hd0 : 0<d := by linarith
  have hz0 : 0<Z := zero_lt_one.trans_le hZ
  have hu0 : 0<Z^d := Real.rpow_pos_of_pos hz0 _
  have hu1 : 1 ≤ Z^d := Real.one_le_rpow hZ hd0.le
  refine ⟨?_,?_⟩
  · intro s
    have hh : 1 ≤ (Z^d)^(ell s/d) := Real.one_le_rpow hu1 (div_nonneg (hell s) hd0.le)
    linarith
  · intro selected
    have hf : (2:ℝ)^selected.card ≤ (2:ℝ)^Fintype.card Slot :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ selected)
    have hp : (2:ℝ)^selected.card ≤ (Z^d)^ε := by
      rw [←Real.rpow_mul hz0.le]
      exact (hf.trans ht).trans (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith))
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
      ←Real.rpow_sum_of_pos hu0,Real.rpow_add hu0]
    calc
      _  ≤  (Z^d)^ε*(Z^d)^(∑s:selected,ell s/d) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu0.le _)
      _ = _ := mul_comm _ _

section Source
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem weighted_sourceMoment_fiber_prime_geometry_eventually
    {D : Cycle25.Weighted.MomentData} (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧ ∀d : ℝ,1/200 ≤ d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=>D.ell s/d)→(∀s,(B.external s).re=17/50)→
      ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      let f:=B.fiber bin j J K hne
      (∀s t,s≠t→Disjoint
        (livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))
        (livePrimes M H (f.profile t) (f.upper t) ((Z^d)^(f.widths t)))) ∧
      ∀selected : Finset (Fin D.N),
        (∀s:selected,1 ≤ 2*(Z^d)^(f.widths s)) ∧
        (∏s:selected,2*(Z^d)^(f.widths s)) ≤ 
          (Z^d)^((∑s:selected,f.widths s)+εg) ∧
        ∀p : selected→Ideal O,
        p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))→
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s:selected,p s) ∧
        (∀s:selected,((p s).absNorm:ℝ) ≤ 2*(Z^d)^(f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖=1 ∧
        ‖star (∏s:selected,primeProfile (f.profile s) ((Z^d)^(f.widths s)) (f.external s) (p s))/
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖ ≤ 1 := by
  filter_upwards [weighted_sourceMoment_separation_eventually D.ell D.slots_injective,
    weighted_sourceMoment_capacity_eventually D.ell (fun s=>(D.slots_bounds s).1.le) εg hεg,
    sourceMoment_fiber_large_eventually M H hH F.S F.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin j J K hne
  have hprofile : B.profile=(fun _=>(F.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0<d := by linarith
  have hu : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths bin j J K hne
  dsimp only
  change (∀s t,s≠t→Disjoint
      (livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s)))
      (livePrimes M H (B.profile t) (B.upper t) ((Z^d)^(B.widths t)))) ∧ _
  refine ⟨?_,?_⟩
  · intro s t hst
    rw [hprofile,hupper,hwidths]
    exact weighted_sourceMoment_live_disjoint M H F (fun s=>D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1 ≤ 2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s)) ≤ (Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=>hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=>livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=>livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=>hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ) ≤ 2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact weighted_sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖ ≤ 1
        rw [hprofile,hwidths]
        exact weighted_sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) (fun s:selected=>B.external s) hu (fun s=>hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.Cycle25ProbeHighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentDetectorMomentPrimeGeometry -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentInverseMarkedReferencePrimeGates; sha256 ec082d457be367185baef0746540eec6cb4f3e1cbcbece9cc3b5f15c0434ddc4 -/
section
                                                                              
                                                               
                                                                           
                                                                       
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O

theorem weighted_deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0<ell s) :
    ∀ᶠZ:ℝ in atTop,1 ≤ Z ∧ ∀d:ℝ,0<d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0 ≤ Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem weighted_deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem weighted_deleted_source_live_prime {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0<X)(ζ:ℂ)(hζ:ζ.re ≤ 1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)<X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖ ≤ 1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact Cycle25ProbeHighRowFamily.weighted_sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentInverseMarkedReferencePrimeGates -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentInverseMarkedReferenceDeletedEnergy; sha256 1aed5d04ec091e9405c716b5aa1a2155cbd94cba123cb29c6772cef834f89f6d -/
section
                                                                                 
                                                                    
                                                                                
                                                                              
                                                                         
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT
open InverseInitialDetectorSource
open InverseMoment InverseInitialProfile InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialEnergyCallerWindow InverseInitialExcludedPeriod
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open IdealMobiusDivisorSum Filter
local notation "O"=>HeckeFamily.O

theorem weighted_deletedSelectedSource_tuple {ι:Type*}[Fintype ι](data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (U r bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O):
    deletedSelectedSource data M H W V U r 0 0 bW b ell ζ u=
      ∑x:Tuple (fun i=>livePrimes M H (V i) (b i) (U^(ell i))),
        (∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i).val)/
          idealCoeff (deletedBase data) (x i).val)*
        originalTotalPolynomial (originalSource U r bW) (∏i,(x i).val)
          (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u := by
  rw [sum_tuple_original (fun i=>livePrimes M H (V i) (b i) (U^(ell i)))
    (fun x=>(∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i))/
      idealCoeff (deletedBase data) (x i))*
      originalTotalPolynomial (originalSource U r bW) (∏i,x i)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u)]
  unfold deletedSelectedSource
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_prod,map_prod,Finset.prod_div_distrib]
  have ht:twistedProfile W 0 0=W:=by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht]
  rfl

theorem weighted_deleted_source_energy {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao ≤ bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀ ≤ U →
    ∀{ι:Type}[Fintype ι],Fintype.card ι ≤ K →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(ell:ι→ℝ)(ζ:ι→ℂ),
      (∀i,0 ≤ ell i) → (∀i,(ζ i).re ≤ 1) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint
        (fun i=>livePrimes M H F.W 2 (U^(ell i)))) →
      (∀i,((deletedBase data).modulus.absNorm:ℝ)<U^(ell i)) →
    ∀r:ℝ,0 ≤ r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀j∈idealDivisors (∏P∈excluded data,P),
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2 ≤ U) → ∀θ:ℝ,
      (∑u∈rows,‖deletedSelectedSource data M H (childLogTest W θ) (fun _=>F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _=>2) ell ζ u‖^2) ≤ 
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩:=padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩:=eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0:U₀ ≤ U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hUp:0<U:=zero_lt_one.trans hUone
  have hjshift: r-eta ≤ shiftedExponent data U r j ∧ shiftedExponent data U r j ≤ r ∧
      U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ):=
    (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  let L:ι→Finset (Ideal O):=fun i=>livePrimes M H F.W 2 (U^(ell i))
  let coeff:ι→Ideal O→ℂ:=fun i P=>star (primeProfile F.W (U^(ell i)) (ζ i) P)/
    idealCoeff (deletedBase data) P
  have hg (i:ι)(P:Ideal O)(hP:P∈L i):
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖coeff i P‖ ≤ 1:=
    weighted_deleted_source_live_prime F data M H _ (Real.rpow_pos_of_pos hUp _) (ζ i) (hζ i) (hlarge i) P hP
  have hratio (i:ι)(P:Ideal O)(hP:P∈L i):((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2:=
    F.complex_support (Finset.mem_filter.mp hP).2
  have hh:=henergy U hU0 hK L ell coeff hell
    (fun i P hP=>(hg i P hP).1)
    (fun i P hP=>weighted_deletedBase_supported data P (hg i P hP).2.2.1)
    hdis hratio (fun i P hP=>(hg i P hP).2.2.2.2)
    (fun i P hP=>by rw [hqset];exact (hg i P hP).2.1)
    (fun _=>F.W) (fun _=>F.complex_support)
    (fun i P hP=>(Finset.mem_filter.mp hP).2)
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rows hrows θ
  simpa only [weighted_deletedSelectedSource_tuple,L,coeff] using hh

end SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentInverseMarkedReferenceDeletedEnergy -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.MomentInverseMarkedReferenceFiberEnergy; sha256 d4a2cf2d0df59d8444accd38e5df98068f96d06bb81f945792572927be7712e0 -/
section
                                                                               
                                                                       
                                                                                 
                                                                       
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem weighted_fiber_reference_energy {D:Cycle25.Weighted.MomentData}
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao ≤ bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀ ≤ U →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
      {Label Slot:Type}{a ε tstar T allowance:ℝ}{i:ℕ}
      (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot),
      F.rowData=data → selected.card ≤ K →
      (∀s∈selected,F.profile s=S.W) → (∀s∈selected,F.upper s=2) →
      (∀s∈selected,0 ≤ F.widths s) → (∀s∈selected,(F.external s).re ≤ 1) →
      (((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected)) →
      (∀s∈selected,((deletedBase data).modulus.absNorm:ℝ)<U^(F.widths s)) →
      0 ≤ F.r → F.r+2*(∑s∈selected,F.widths s)<1 →
      2*F.r+8*(∑s∈selected,F.widths s)<3 → ∀v:ℝ,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
        F.physicalProduct selected u‖^2) ≤ C*U^(1+εm)*((1+‖v‖)^degree)^2 := by
  have hsor (b:Bool):Function.support (orientedProfile b W)⊆Set.Icc ao bo := by
    cases b
    · exact hsW
    · intro x hx
      apply hsW
      simpa [orientedProfile] using hx
  have hWor (b:Bool):ContDiff ℝ ∞ (orientedProfile b W) := by
    cases b
    · exact hW
    · exact Complex.conjCLE.contDiff.comp hW
  choose J hj using fun b:Bool=>weighted_deleted_source_energy S (orientedProfile b W) ao bo hao hab
    (hsor b) (hWor b) εm hεm K
  refine ⟨∑b:Bool,J b,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun b:Bool=>hj b data
  let Tbad:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:ℝ:=((Tbad.card:ℝ)+1)^2*(∑b:Bool,C b)
  have hCsum:0<∑b:Bool,C b:=Finset.sum_pos (fun b _=>hC b) Finset.univ_nonempty
  refine ⟨Ctotal,max (U₀ false) (U₀ true),by dsimp [Ctotal];positivity,
    lt_max_of_lt_left (hU₀ false),?_⟩
  intro U hU M neM H Label Slot a ε tstar T allowance i F selected hdata hK hprofile hupper
    hell hext hdis hlarge hr hfirst hsecond v
  have hUb (b:Bool):U₀ b ≤ U:=by cases b <;> exact le_trans (by simp) hU
  have hUone:1<U:=(hU₀ false).trans_le (hUb false)
  have hpr (s:selected):F.profile s=S.W:=hprofile s s.property
  have hup (s:selected):F.upper s=2:=hupper s s.property
  have hprof:(fun s:selected=>F.profile s)=(fun _=>(S.W:ℝ→ℂ)):=funext hpr
  have hups:(fun s:selected=>F.upper s)=(fun _=>2):=funext hup
  have hslots:∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (1:ℝ) (F.upper s) := by
    intro s hs x hx
    rw [hprofile s hs] at hx
    rw [hupper s hs]
    exact S.complex_support hx
  have hlarge':∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<1*U^(F.widths s):=by
    simpa only [hdata,one_mul] using hlarge
  have hphys:=fiber_child_rows_le_deleted_sources F selected W v bo (fun _=>1) hUone
    (fun x hx=>(hsW hx).2) hslots hlarge'
  rw [hdata] at hphys
  let rows:Finset O:=F.rows.image (fun u=>u.val)
  have hsum (f:O→ℝ):(∑u∈rows,f u)=∑u∈F.rows,f u.val:=
    Finset.sum_image (fun u _ w _ he=>Subtype.ext he)
  have hrows:∀u∈rows,‖eisEmbedding u‖^2 ≤ U := by
    intro u hu
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact F.row_norm w hw
  have hpow (b:Bool):((1+‖orientedFrequency b v‖)^(J b))^2 ≤ 
      ((1+‖v‖)^(∑b:Bool,J b))^2 := by
    have hn:‖orientedFrequency b v‖=‖v‖:=by cases b <;> simp [orientedFrequency]
    rw [hn]
    apply pow_le_pow_left₀ (by positivity)
    apply pow_le_pow_right₀ (by linarith [norm_nonneg v])
    exact Finset.single_le_sum (fun b _=>Nat.zero_le _) (Finset.mem_univ b)
  have hterm (j:Ideal O)(hj:j∈Tbad):
      (∑u∈F.rows,‖deletedSelectedSource data M H
        (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
        (fun s:selected=>F.profile s) U (shiftedExponent data U F.r j)
        0 0 bo (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
        (fun s:selected=>F.external s) u.val‖^2) ≤ 
      (∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2 := by
    rw [hprof,hups]
    have hdis':((Finset.univ:Finset selected):Set selected).PairwiseDisjoint
        (fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
      have heL:fiberLists F selected=(fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
        funext s
        dsimp only [fiberLists]
        rw [hpr s,hup s]
      rwa [heL] at hdis
    have hh:=hb F.reverse U (hUb F.reverse) (by simpa using hK)
      M H (fun s:selected=>F.widths s) (fun s:selected=>F.external s)
      (fun s=>hell s s.property) (fun s=>hext s s.property) hdis'
      (fun s=>hlarge s s.property) F.r hr
      (by simpa only [Finset.sum_coe_sort] using hfirst)
      (by simpa only [Finset.sum_coe_sort] using hsecond) j hj rows hrows (orientedFrequency F.reverse v)
    rw [hsum] at hh
    refine hh.trans ?_
    apply mul_le_mul _ (hpow F.reverse) (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ F.reverse)
  refine hphys.trans ?_
  change (Tbad.card:ℝ)*(∑j∈Tbad,_) ≤ _
  calc
    _ ≤ (Tbad.card:ℝ)*(∑j∈Tbad,(∑b:Bool,C b)*U^(1+εm)*
        ((1+‖v‖)^(∑b:Bool,J b))^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=(Tbad.card:ℝ)^2*(∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _ ≤ Ctotal*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0 ≤ (Tbad.card:ℝ) by positivity]

end SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference

end

end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.MomentInverseMarkedReferenceFiberEnergy -/
