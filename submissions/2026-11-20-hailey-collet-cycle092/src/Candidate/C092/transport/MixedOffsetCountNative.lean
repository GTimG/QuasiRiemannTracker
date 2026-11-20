/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native source metadata, with no moment or cardinality premise. -/
import Candidate.C092.transport.MixedOffsetCountRectangles
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorBatch
open QRH.Record12518109Count Cycle25ProbeFinalAssembly QRH.Cycle092.PacketJoinE49

/-- These fields describe a literal native Batch. They contain only exact
source dictionary/profile/width equalities and the original supported rows. -/
structure Presented (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D)
    (η : Character) (Z d a tstar T allowance : ℝ) (i : ℕ) where
  batch : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
    (Z^d) a D.ε tstar T allowance i
  lower : ∀u∈batch.rows,Z^(1/100:ℝ)≤rowNorm u
  data : batch.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η
  profile : batch.profile=(fun _ x=>(S.w x:ℂ))
  widths : batch.widths=(fun s=>D.ell s/d)
  upper : batch.upper=(fun _=>2)
  real : ∀s,(batch.external s).re=17/50

structure Slice {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D}
    {η : Character} {Z d a tstar T allowance : ℝ} {i : ℕ}
    (P : Presented D S η Z d a tstar T allowance i) where
  bin : P.batch.Bin
  label : Sum Bool (RayQuotient.Characters S.modulus ⊤)
  left : Fin (dyadicLength (Z^d))
  right : Fin (dyadicLength (Z^d))
  nonempty : (P.batch.fiberRows bin label left right).Nonempty

abbrev Slice.fiber {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D}
    {η : Character} {Z d a tstar T allowance : ℝ} {i : ℕ}
    {P : Presented D S η Z d a tstar T allowance i} (F : Slice P) :=
  P.batch.fiber F.bin F.label F.left F.right F.nonempty

/-- Genuine tangent source moments imply both rectangle counts for every
later native cutoff/fiber. No moment or per-fiber count estimate is supplied
by the caller. J,C precede every live scale, cutoff and bank descriptor. -/
theorem actual_rectangle_counts (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0< mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
    (∀s,D.ell s≤ mesh D.t/200) →
    ∀η : Character,∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀d : ℝ,(1/200:ℝ)≤d →
    ∀ (a tstar T allowance height : ℝ) (i : ℕ)
      (P : Presented D S η Z d a tstar T allowance i) (F : Slice P),
      1/2<a → D.t≤1/10000000 → 0≤height →
      (∀s,|(P.batch.external s).im|≤height) →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      anchorLeft≤F.fiber.r → F.fiber.r≤anchorTop →
      anchorLeft≤2*F.fiber.m → 2*F.fiber.m≤anchorTop →
      (F.fiber.rows.card:ℝ)≤(12*(1+height)*(C*(1+height)^J))*
        (Z^d)^(1-(2*a-1)*(Return.aI (F.fiber.q/(2*a-1))+Return.kI (F.fiber.q/(2*a-1))*F.fiber.r)+
          2*F.fiber.q*D.t+2*D.ε+(2*a-1)*F.fiber.mesh+D.t) ∧
      (F.fiber.rows.card:ℝ)≤(192*(1+height)*(C*(1+height)^J))*
        (Z^d)^(1-(2*a-1)*(Return.aI (F.fiber.q/(2*a-1))+2*Return.kI (F.fiber.q/(2*a-1))*F.fiber.m)+
          2*F.fiber.q*D.t+4*D.ε+(2*a-1)*F.fiber.mesh+D.t) := by
  have hs:=tangent_fiber_moments hβ
  choose mesh hm hsource using fun t : {t:ℝ//0<t}=>hs t.val t.property
  let chooseMesh : ℝ→ℝ:=fun t=>if ht:0<t then mesh ⟨t,ht⟩ else 1
  refine ⟨chooseMesh,?_,?_⟩
  · intro t ht;simpa only [chooseMesh,dif_pos ht] using hm ⟨t,ht⟩
  intro D S hfine η
  have hfi : ∀s,D.ell s≤ mesh ⟨D.t,D.t_pos⟩/200 := by
    simpa only [chooseMesh,dif_pos D.t_pos] using hfine
  obtain ⟨J,C,hC,hsource⟩:=(hsource ⟨D.t,D.t_pos⟩ S rfl hfi) η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a tstar T allowance height i P F ha ht hh him hf hr hr' hm hm'
  have hi:=hZ.2 P.batch.rows P.lower d hd a tstar T allowance i P.batch (fun _ hu=>hu)
    P.data P.profile P.widths (fun s=>congrFun P.upper s) P.real
    F.bin F.label F.left F.right F.nonempty height hh him
  exact rectangle_counts F.fiber (Real.one_lt_rpow hZ.1 (by linarith)) ha (by positivity) hh hf
    D.t_pos ht hi hr hr' hm hm'

#print axioms actual_rectangle_counts
end
end QRH.Cycle092.MixedOffsetCount
