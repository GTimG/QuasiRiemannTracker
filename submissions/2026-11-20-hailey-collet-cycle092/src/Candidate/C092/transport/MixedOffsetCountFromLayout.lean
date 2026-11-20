/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Construct the actual remaining-middle record from one original bank class. -/
import Candidate.C092.transport.MixedOffsetCountLayoutFacts
import Candidate.C092.transport.MixedOffsetCountRoutes
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount.MiddleBank
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckeDetectorPhysicalSelection
open QRH.Record12518109Count Cycle25ProbeFinalAssembly QRH.Cycle092.PacketJoinE49
open QRH.Cycle092.MixedOffsetBank
variable {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D} {η : Character} {Z : ℝ}

/-- Every native presentation, common-row inclusion, full amplitude mean,
current/prior dyad and prior-long gate is built from the genuine bank.
Remaining inputs are source metadata equalities and explicit geometric
admission/collar gates. No count, moment or physical amplitude bound is a field. -/
def ofLayout (rows : Finset FreeRow) (d a t₀ γ T allowance : ℝ) (i : ℕ)
    (B : SourceBank S.modulus ⊤ le_top S.S S.exclusions η rows (Z^d) a D.ε t₀ γ T allowance i)
    (L : BankLayout (Slot:=Fin D.N) B)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : (L.common σ).Nonempty) (j : Offset)
    (first : firstShort (inverseLength (Z^d) σ)=some j)
    (source_lower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)
    (source_profile : L.profile=(fun _ x=>(S.w x:ℂ)))
    (source_widths : L.widths=(fun s=>D.ell s/d)) (source_upper : L.upper=(fun _=>2))
    (source_real : ∀s,(L.external s).re=17/50)
    (height εa factor : ℝ)
    (hd : (1/200:ℝ) ≤ d) (ha : 51/100<a) (hdelta : 2*a-1 ≤ 3/4)
    (hh : 0 ≤ height) (hfreq : 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height)
    (hext : ∀s,|(L.external s).im| ≤ height)
    (hgamma : 0 ≤ γ) (hcutmin : 1 ≤ t₀-γ) (hcutmax : t₀ ≤ 3/2)
    (hcollar : 0 ≤ εa) (hsupport : D.ε ≤ 3*εa)
    (havailable : Return.window.Available (2*a-1)
      ((classMean L.slots ((2*a-1)/2) L.binWidth L.widths L.bin)/(2*a-1)))
    (hbase : t₀=Return.cutoffI (2*a-1)
      ((classMean L.slots ((2*a-1)/2) L.binWidth L.widths L.bin)/(2*a-1)))
    (hinv : anchorLeft ≤ inverseLength (Z^d) σ j)
    (hinv' : inverseLength (Z^d) σ j ≤ anchorTop)
    (hord : anchorLeft ≤ 2*ordinaryLength (Z^d) σ j)
    (hord' : 2*ordinaryLength (Z^d) σ j ≤ anchorTop)
    (hscale : (2*a-1)*factor ≤ 5/6-(2*a-1)) : MiddleBank D S η Z := by
  let pres (k : Offset) : Presented D S η Z d a (cutoff t₀ γ k) T allowance i :=
    ⟨L.batch k,source_lower,rfl,source_profile,source_widths,source_upper,source_real⟩
  let slice (k : Offset) : Slice (pres k) :=
    ⟨L.bin,σ.1,σ.2.1 k,σ.2.2 k,hne.mono (L.common_subset_fiber σ k)⟩
  let wz : ∀u∈rows,SupportedWitness
      (sourceDetectorFamily S.S S.exclusions.prime η u (rayCubeFamily S.modulus ⊤ le_top u))
      (Z^d) a D.ε t₀ T allowance i := fun u hu=>by
    simpa only [cutoff,offset,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,sub_zero] using B.witness 0 ⟨u,hu⟩
  let baseBatch:=retainedSourceBatch S.modulus ⊤ le_top S.S S.exclusions η rows L.u₀ L.member
    (Z^d) a D.ε t₀ T allowance i wz L.row_norm L.slots L.profile L.upper L.widths L.external L.mesh L.binWidth
    L.mesh_nonneg L.binWidth_pos L.widths_pos L.widths_mesh L.supply
  let base : Presented D S η Z d a t₀ T allowance i :=
    ⟨baseBatch,source_lower,rfl,source_profile,source_widths,source_upper,source_real⟩
  refine {
    d:=d,a:=a,T:=T,allowance:=allowance,height:=height
    q:=classMean L.slots ((2*a-1)/2) L.binWidth L.widths L.bin
    t₀:=t₀,γ:=γ,meshBank:=L.mesh,εa:=εa,factor:=factor,i:=i,j:=j
    d_min:=hd,a_min:=ha,delta_max:=hdelta,height_nonneg:=hh,frequency:=hfreq
    gamma_nonneg:=hgamma,cutoff_min:=hcutmin,cutoff_max:=hcutmax,mesh_nonneg:=L.mesh_nonneg
    collar_nonneg:=hcollar,support_collar:=hsupport,available:=havailable,baseline_cutoff:=hbase
    base:=base,current:=pres j,prior:=pres (previous j),currentSlice:=slice j,priorSlice:=slice (previous j)
    base_nonempty:=⟨L.u₀,L.member⟩,base_mean:=?_,base_height:=hext,current_height:=hext,prior_height:=hext
    base_mesh:=le_refl _,current_mesh:=le_refl _,current_mean:=?_
    inverse_min:=?_,inverse_max:=?_,ordinary_min:=?_,ordinary_max:=?_,prior_long:=?_
    directed_scale:=hscale,common:=L.common σ,common_base:=?_,common_current:=?_,common_prior:=?_ }
  · intro u hu
    exact rowMean_eq rows L.slots (Z^d) ((2*a-1)/2) L.binWidth L.binWidth_pos L.widths _ L.bin u
      (Finset.mem_filter.mpr ⟨hu,L.fixed_phase u hu⟩)
  · exact L.fiber_mean σ hne j
  · rw [show (slice j).fiber.r=inverseLength (Z^d) σ j from (L.fiber_lengths σ hne j).1];exact hinv
  · rw [show (slice j).fiber.r=inverseLength (Z^d) σ j from (L.fiber_lengths σ hne j).1];exact hinv'
  · rw [show (slice j).fiber.m=ordinaryLength (Z^d) σ j from (L.fiber_lengths σ hne j).2];exact hord
  · rw [show (slice j).fiber.m=ordinaryLength (Z^d) σ j from (L.fiber_lengths σ hne j).2];exact hord'
  · exact (L.first_short σ hne j first).2
  · exact class_subset rows L.labels (fun k u=>(L.witness k u).left) (fun k u=>(L.witness k u).right) σ
  · exact L.common_subset σ hne j
  · exact L.common_subset σ hne (previous j)

#print axioms ofLayout
end
end QRH.Cycle092.MixedOffsetCount.MiddleBank
