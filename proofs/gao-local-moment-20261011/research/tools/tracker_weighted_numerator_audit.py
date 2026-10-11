#!/usr/bin/env python3
"""Exact scalar retuning screen only: no new analytic theorem or Lean/kernel run.

Formulas follow Akash Levy, Weighted numerator moments, at tracker pin
0f78cd9b99ba745c7b475f76a971d6107229906b. This independent implementation
reconstructs the rational exponents and checks every subrectangle using
Bernstein coefficients; point samples never certify positivity.
"""
from fractions import Fraction as Q
from math import comb
import json
import argparse
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = "0f78cd9b99ba745c7b475f76a971d6107229906b"
SOURCE_INPUT = "numerics/results/tracker_weighted_numerator_sources.json"
REPORT = ROOT / "numerics/results/tracker_weighted_numerator_audit.json"

def const(q): return {(0, 0): Q(q)}
def add(*parts):
    out = {}
    for p in parts:
        for ij, c in p.items(): out[ij] = out.get(ij, Q(0)) + c
    return {ij:c for ij,c in out.items() if c}
def smul(c,p): return {ij:c*v for ij,v in p.items() if c*v}
def mul(p,q):
    out={}
    for (i,j),a in p.items():
        for (k,l),b in q.items(): out[i+k,j+l]=out.get((i+k,j+l),Q(0))+a*b
    return {ij:c for ij,c in out.items() if c}
def value(p,d,x): return sum(c*d**i*x**j for (i,j),c in p.items())
def bernstein(p,box):
    d0,d1,x0,x1=box
    n=max(i for i,j in p);m=max(j for i,j in p)
    local={}
    for (i,j),a in p.items():
        for k in range(i+1):
            for l in range(j+1):
                local[k,l]=local.get((k,l),Q(0))+a*comb(i,k)*comb(j,l)*d0**(i-k)*x0**(j-l)*(d1-d0)**k*(x1-x0)**l
    vals=[sum(local.get((k,l),Q(0))*Q(comb(i,k),comb(n,k))*Q(comb(j,l),comb(m,l)) for k in range(i+1) for l in range(j+1)) for i in range(n+1) for j in range(m+1)]
    # Re-expand every Bernstein basis element, checking the polynomial identity
    # coefficient by coefficient (not by evaluating a finite sample of points).
    recovered={}
    for i in range(n+1):
        for j in range(m+1):
            beta=vals[i*(m+1)+j]
            for k in range(i,n+1):
                for l in range(j,m+1):
                    term=beta*comb(n,i)*comb(n-i,k-i)*comb(m,j)*comb(m-j,l-j)*(-1)**(k-i+l-j)
                    recovered[k,l]=recovered.get((k,l),Q(0))+term
    assert {ij:q for ij,q in recovered.items() if q}=={ij:q for ij,q in local.items() if q}
    return vals

def certify(p,box,depth=0):
    b=bernstein(p,box)
    if min(b)>=0:
        return [{'box':[str(q) for q in box],'bernstein_degree':[max(i for i,j in p),max(j for i,j in p)],'bernstein_coefficients':[str(q) for q in b],'minimum':str(min(b))}]
    assert depth<30, ('subdivision limit',box)
    d0,d1,x0,x1=box
    if d1-d0>=x1-x0:
        z=(d0+d1)/2;boxes=[(d0,z,x0,x1),(z,d1,x0,x1)]
    else:
        z=(x0+x1)/2;boxes=[(d0,d1,x0,z),(d0,d1,z,x1)]
    return sum((certify(p,b,depth+1) for b in boxes),[])

def coverage(leaves, domain):
    """Finite closed rectangles: containment, disjoint interiors, full area."""
    a,b,c,d=domain
    boxes=[tuple(Q(q) for q in leaf['box']) for leaf in leaves]
    for x0,x1,y0,y1 in boxes:
        assert a<=x0<x1<=b and c<=y0<y1<=d, 'Leaf outside domain'
    for i,(x0,x1,y0,y1) in enumerate(boxes):
        for u0,u1,v0,v1 in boxes[i+1:]:
            assert min(x1,u1)<=max(x0,u0) or min(y1,v1)<=max(y0,v0), 'Overlapping leaf interiors'
    area=sum((x1-x0)*(y1-y0) for x0,x1,y0,y1 in boxes)
    assert area==(b-a)*(d-c), 'Uncovered area'
    # Finite unions of closed rectangles are closed. A nonempty relative-open
    # complement in a nondegenerate parent rectangle has positive area.
    # Consequently these exact checks imply coverage including boundaries.
    return dict(contained=True,interiors_disjoint=True,covers_closed_domain=True,
                leaf_area=str(area),domain_area=str((b-a)*(d-c)))


def range_certificates(J,RJ,D,P,delta,x,kappa):
    box=(Q(0),Q(3,4),Q(0),Q(1,2))
    residuals={
        'D_positive':D,'P_positive':P,'J_positive':J,
        'R_at_least_one_minus_delta':add(RJ,smul(-1,mul(add(const(1),smul(-1,delta)),J))),
        'R_at_most_one':add(J,smul(-1,RJ)),
        'R_density_upper':add(mul(add(const(Q(76,75)),smul(-Q(2,3),delta)),J),smul(-1,RJ)),
    }
    certs={}
    for name,poly in residuals.items():
        coefficients=bernstein(poly,box)
        assert min(coefficients)>=0
        if name.endswith('_positive'): assert min(coefficients)>0
        certs[name]=dict(bernstein_coefficients=[str(q) for q in coefficients],minimum=str(min(coefficients)))
    old_lower=1-Q(3,8)-Q(17,50)
    old_upper=1+Q(3,8)-Q(17,50)
    wt_lower=(3*(1-Q(3,4))+1)/4-Q(17,50)
    wt_upper=1-Q(17,50)+Q(3,8)/(12*kappa)
    assert 0<old_lower<=old_upper<2
    assert 0<wt_lower<=wt_upper<2
    # These bounds follow for every point from certified 1-delta<=R<=1,
    # 0<=delta<=3/4, 0<=q=delta*x<=3/8, rather than sampled row slopes.
    return dict(domain=[str(q) for q in box],denominator_cleared_certificates=certs,
        count_range='1-delta <= R <= 1',
        density_bound='R<=76/75-2delta/3 on the same full rectangle; preserves the source rowCount_density_bound used for d<=1/2',
        old_slope=dict(formula='R+delta/2-17/50',lower=str(old_lower),upper=str(old_upper)),
        weighted_slope=dict(formula='(3R+1)/4-17/50+delta*x/(12kappa)',lower=str(wt_lower),upper=str(wt_upper)),
        universal_row_slope_upper='2')


def low_range_certificate(ell):
    intercept=(5*ell-1)/8
    slopes=(Q(-1),-Q(7,8))
    endpoint_values=[-v+max(Q(0),5*ell-1+v)/8 for v in (Q(0),ell)]
    assert ell>0 and intercept<0 and all(v<0 for v in slopes)
    assert all(v<=0 for v in endpoint_values)
    return dict(domain=['0',str(ell)],
        expression='-v+max(0,5ell-1+v)/8 = max(-v,(5ell-1-7v)/8)',
        affine_slopes=[str(v) for v in slopes],second_intercept=str(intercept),
        endpoint_values=[str(v) for v in endpoint_values],
        proof='The expression is the maximum of two affine functions, hence convex. Both endpoint values are nonpositive, so the convex interpolation bounds the entire interval by zero. The two negative slopes also prove monotonicity on v>=0.',
        entire_interval_nonpositive=True)


def coverage_negative_controls():
    domain=(Q(0),Q(1),Q(0),Q(1))
    cases=[
        [{'box':['0','1','0','1']},{'box':['0','1','0','1']}],
        [{'box':['0','1/2','0','1']}],
        [{'box':['-1','0','0','1']}],
    ]
    for leaves in cases:
        try: coverage(leaves,domain)
        except AssertionError: pass
        else: raise AssertionError('Invalid covering accepted')
    return dict(overlapping_leaves_rejected=True,missing_area_rejected=True,outside_leaf_rejected=True)

def budget_feasibility(theta,ell,lx,ly,h,endpoint,extension,extended):
    """Universal positive-parameter ledger, conditional on retuned source contracts.

    This records coefficient comparisons, rather than testing isolated choices
    of Delta, N, ellMin or degree J. The constructor provides, for every
    Delta>0, positive t<=1e-8, epsilon,e<=t/2000, (N+8)eps<=t,
    sigma<=min(t/2,ellMin/4), e<=ellMin/4. A uniform J is obtained later.
    """
    cap=Q(1,10**8); central=raw=Q(1,80000)
    contour_e=16-6*ly
    central_coeff=16+ell+(159+12+contour_e)/2000
    # Exact central ledger =159epsilon+(12+contour_e)e+(N+8)eps+(15+ell)t.
    assert central_coeff*cap<central
    # WeightedSourceLoss: first remove d<=1, then mesh/mass/boxes/annuli<=t,
    # moment loss<=2t, delta<=3/4, q<=3/8. Every coefficient is nonnegative.
    packet_epsilon=Q(3,4)*159
    packet_t=3+Q(17,25)+1+Q(27,4)+Q(1,2)+Q(3,16)+Q(3,16)+Q(1,12)+ell
    assert packet_epsilon<=120 and packet_t<=13
    # The sufficient loss envelope used by weighted_source_fixed_budget is
    # 159epsilon+9e+(N+8)eps+(14+ell)t. Subtracting the packet bound
    # leaves 39epsilon+9e+(N+6)eps+(1+ell)t, all nonnegative.
    assert 159-120>=0 and 9>=0 and 8-2>=0 and 14+ell-13>=0
    # Adding the 16e scale shift and a t height reserve then fits central.
    assert (12+contour_e)-(9+16)>=0
    assert extended-central==raw
    residuals={
        'central':central-central_coeff*cap,
        'detector_per_epsilon':Q(1,2)-(Q(288,10000)+Q(10,1000)),
        'phase_per_epsilon':1-(Q(8,10000)+Q(1,1000)),
        'geometric':Q(1,20)-(Q(1,2)+Q(8,2000)+Q(1,8))*cap,
        'principal':Q(1,4000)-(Q(1,2)+Q(1,8))*cap,
        'window_per_minimum_slot':theta-Q(1,2),
        'floor':Q(1,100)-(Q(26,2000)+1+1+ell+Q(1,8)+Q(1,2))*cap,
        'high_saving':raw-(Q(1,2)+Q(1,8)+Q(1,8))*cap,
        'weighted_top':extension-3*cap,
        'conductor_top':Q(7,8)-h-3*cap,
        'count_loss_gate':Q(1,32)-(Q(159,2000)+9)*cap,
        'floor_coefficient_envelope':26-(12+contour_e),
        'weighted_epsilon_envelope':120-packet_epsilon,
        'weighted_t_envelope':13-packet_t,
        'weighted_packet_to_central_e':12+contour_e-25,
        'row_extension_to_advertised_bound':endpoint-2*extension-extended,
    }
    assert all(q>0 for q in residuals.values())
    # Late height construction is tau=min(cost/3200,1/800,t/(4*(J+7))).
    # For all J>=0 multiply each desired inequality by positive 4(J+7).
    # These exact nonnegative affine coefficients prove the universal gates.
    height_polynomial_residuals={
        'tau_lt_t':[Q(27),Q(4)],                 # 4(J+7)-1
        'twice_tau_lt_t':[Q(26),Q(4)],           # 4(J+7)-2
        'height_budget':[Q(26),Q(2)],            # 4(J+7)-2(1+J)
        'eps_height_strict_for_eps_le_one':[Q(22),Q(4)], # 4(J+7)-6
    }
    assert all(v[0]>0 and all(q>=0 for q in v) for v in height_polynomial_residuals.values())
    assert Q(1,800)<Q(1,400) and Q(4,3200)<Q(1,200)
    assert 2000*Q(1,2000)==1
    assert Q(1,2)+Q(1,4)==Q(3,4)
    # Source constants must change together with their physical definitions.
    costs={
        'centralScale_amplitude':1-ly,
        'centralScale_constant':Q(4,25)*lx-Q(33,50),
        'centralScale_e':contour_e,
        'central_prime_normalization':-Q(4,25)*ell,
        'floor_prime_normalization':-Q(3,20)*ell,
        'contour_arithmetic_exponent':6+3*ell,
        'slot_rescaling_factor_from_total_one_sixth':6*ell,
        'signal_shift':-(4+Q(43,500))/6,
    }
    return dict(
        status='PASS_EXACT_PROPOSED_LEDGER_FEASIBILITY_ONLY',
        quantifiers='For every Delta>0, every constructor-produced N,rmin and common positive mesh; analytic degree J>=0 chosen after fine/source data; height tau chosen after J.',
        t_choice='min(Delta/8,1/100000000)',t_cap=str(cap),
        constructor_choices={'small':'t/(N+2000)','epsilon':'min(small/2,rmin*t/2,1/2000)','e':'min(epsilon/(10000*(1+t)),ellMin/4,small/2)','detector_kappa':'epsilon/1000','cost':'epsilon/1000','eps':'small/2','sigma':'min(t/2,ellMin/4)','ellMin':'7*rmin/8'},
        detector_bounds=['288e+8*detector_kappa+2cost<=epsilon/2','8et+detector_kappa<=epsilon','epsilon<rmin*t','0<e<1/1000','0<epsilon<=1/1000','0<detector_kappa<=1'],
        constructor_bounds=['0<t<Delta/4','2000*epsilon<=t','2000*e<=t','(N+8)*eps<=t','0<eps<=1','0<sigma<=min(t/2,ellMin/4)','e<=ellMin/4'],
        central_ledger='159epsilon+(28-6ly)e+(N+8)eps+(15+ell)t',
        central_t_coefficient=str(central_coeff),central_maximum=str(central_coeff*cap),central_allowance=str(central),
        weighted_packet='loss<=120epsilon+2eps+13t; 16e+loss+t<=central ledger',
        weighted_packet_raw_t_coefficient=str(packet_t),weighted_packet_raw_epsilon_coefficient=str(packet_epsilon),
        raw_source_reserve=str(raw),raw_source_target='signal(theta)-1/80000-SZExponent-t',
        normalized_collected_target='signal(theta)-1/80000+t/8+t/8 <= signal(beta)-sigma',
        budget_residuals={k:str(v) for k,v in residuals.items()},
        late_height=dict(choice='min(cost/3200, min(1/800,t/(4*(J+7))))',assumptions='cost>0,t>0,J>=0,0<=eps<=1',
            denominator_cleared_residuals={k:[str(q) for q in v] for k,v in height_polynomial_residuals.items()},
            gates=['0<tau<1/400','4tau<cost/200','tau<t','2tau<=t','2tau(1+J)<=t','tau(2+4eps)<t']),
        recomputed_source_costs={k:str(v) for k,v in costs.items()},
        order='Delta -> t, fine slots -> detector parameters -> fresh source data/count parameters -> analytic common degree -> tau -> characters/rows/heights/tails/threshold',
        scope='Proves feasibility of the proposed scalar budgets from the existing constructor bounds after retuning. Does not construct or validate the new complete analytic source cohort.',
        analytic_adapter_certified=False)

def report():
    source_path=ROOT/SOURCE_INPUT
    evidence=json.loads(source_path.read_text())
    assert evidence["tracker_commit"]==PIN
    assert evidence["best_reported_record"]["theta"]=="10499/12000"
    assert evidence["best_reported_record"]["status"]=="framework-verified"
    assert evidence["all_public_weighted_modules_match_receipt_manifest"] is True
    assert evidence["public_weighted_module_count"]==228
    assert evidence["candidate_nonvanishing_verified"] is False
    theta=Q(8749,10000);ell=Q(1253,7500);b=Q(43,500)
    lx=(1-ell-b)/2;ly=(1-ell+b)/2;h=1-lx+ell
    kappa=Q(3,4);z=Q(17,50);alpha=Q(5,6)
    margin=Q(1,20000);extension=Q(1,10**6);extended_margin=Q(1,40000)
    delta={(1,0):Q(1)};x={(0,1):Q(1)};q=mul(delta,x)
    D=add(const(3),smul(-Q(17,9),x))
    P=mul(add(const(2),smul(-Q(8,9),x)),add(const(1),smul(-1,x)))
    J=add(mul(add(const(alpha),smul(-1,delta)),D),mul(delta,P))
    RJ=add(mul(add(const(1),smul(-1,delta)),J),smul(Q(1,2),mul(mul(add(const(alpha),smul(-1,delta)),delta),P)))
    # Independently assemble each exponent directly, instead of adding their difference.
    old_rest=add(const(Q(1,2)-theta-h/Q(6)-ly/2-ell/2),smul((1-ly+h)/2,delta),smul(ell,q))
    old=add(mul(J,old_rest),smul(h,RJ))
    weighted_rest=add(const(Q(1,2)-theta-h/6-ly/2-ell/2+h/4),smul(Q(1,2),delta),smul(ell-(2*ly-h)/(12*kappa),q))
    weighted=add(mul(J,weighted_rest),smul(3*h/4,RJ))
    difference=add(smul(h/4,add(J,smul(-1,RJ))),smul((ly-h)/2,mul(delta,J)),smul(-(2*ly-h)/(12*kappa),mul(q,J)))
    assert add(weighted,smul(-1,old),smul(-1,difference))=={}
    domains=[('original',old,(Q(0),Q(1,3),Q(0),Q(1,2))),('weighted',weighted,(Q(1,3),Q(3,4),Q(0),Q(1,2)))]
    branches=[]
    for name,numerator,box in domains:
        polynomial=smul(-1,add(numerator,smul(margin,J)))
        leaves=certify(polynomial,box)
        coverage_result=coverage(leaves,box)
        branches.append(dict(name=name,domain=[str(t) for t in box],margin=str(margin),leaf_count=len(leaves),leaves=leaves,coverage=coverage_result))
    checks={}
    def check(name,q,strict=True):
        assert q>0 if strict else q>=0,(name,q)
        checks[name]={'residual':str(q),'strict':strict}
    check('strict_improvement',Q(10499,12000)-theta)
    assert Q(10499,12000)-theta==Q(1,60000)
    assert theta==Q(11,12)-ell/4
    assert theta-(4+b)/6==lx/2+b/12
    check('original_moment_kappa', (1+kappa)/2-Q(7,8),False)
    for name,residual in {
        'positive_b':b,'ell_below_one_fifth':Q(1,5)-ell,
        'X_after_rescaling':lx-ell,'Y_after_rescaling':ly-ell,
        'row_after_rescaling':1-3*ell,'Gram_domination':ly-ell-Q(11,6)*b,
        'low_gram_scale_gap':2*lx-ly-ell,
        'principal_w_contour_reserve':ly/20-(1+h)/1000-Q(1,4000),
        'principal_z_contour_reserve':h/600-Q(1,1000)-Q(1,4000),
        'row_count_supply':ell/h-Q(7,37),'row_extension_supply':5*ell-h,
        'reflected_numerator_short':2*ly-h,'ly_below_half':Q(1,2)-ly,
        'numerator_supply':ell-(2*ly-Q(1,2))/(6*kappa),
        'weighted_frequency_slope_lower':Q(3,4)*(1-Q(3,4))+Q(1,4)-z,
        'coefficient_dilation_slope_per_delta':Q(1,4)-1/(12*kappa),
        'small_row_margin':-(h*(z-Q(1,6))-ly/2+Q(63,5000)),
        'principal_w_margin':ly/20,'principal_z_margin':h/600,
        'Euler_defect_A':-1-(4-6*theta-6*Q(33,200)),
        'Euler_defect_B':-1-(1-theta-Q(19,20)-6*Q(33,200)),
        'extended_row_count_supply':ell/(h+extension)-Q(7,37),
        'extended_reflected_numerator_short':2*ly-h-extension,
        'extended_row_supply':5*ell-h-extension,
        'extended_h_below_one':1-h-extension,
        'extended_endpoint_reserve':margin-2*extension-extended_margin,
    }.items(): check(name,residual)
    for v in [Q(0),ell]: check('low_tuple_'+str(v),v-max(Q(0),5*ell-1+v)/8,False)
    for i,e in enumerate([-theta,-6*Q(33,200),4-5*theta-6*Q(33,200),1-Q(19,20)-6*Q(33,200)]):check('Euler_principal_'+str(i),-theta-e,False)
    def generic(delta,q,R,row):return (1+delta)/2-theta+h*(z-Q(1,6))-(1+delta)*ly/2-ell/2+q*ell+row*(R+delta/2-z)
    check('floor_margin',-generic(Q(1,50),Q(1,100),Q(1),h))
    check('floor_extended_reserve_above_one_hundredth',-generic(Q(1,50),Q(1,100),Q(1),h+extension)-Q(1,100))
    for d in [Q(1,50),Q(3,4)]:check('intermediate_margin_'+str(d),-generic(d,d/2,Q(76,75)-2*d/3,Q(1,2)))
    jb=bernstein(J,(Q(0),Q(3,4),Q(0),Q(1,2)))
    check('J_lower',min(jb))
    # Exact obstruction to copying the incumbent budget.
    wd=Q(89,192);wx=Q(1,2)
    wE=value(weighted,wd,wx)/value(J,wd,wx)
    assert wE>-Q(1,10000)
    # Old theta at new target but old lengths also cannot certify the low bound.
    low_gap=Q(11,12)-Q(167,1000)/4-theta
    assert low_gap==Q(1,60000)>0
    out=dict(status='PASS_SCALAR_RETUNING_ONLY',benchmark=str(Q(10499,12000)),target=str(theta),improvement=str(Q(1,60000)),
        geometry={k:str(v) for k,v in dict(ell=ell,b=b,lx=lx,ly=ly,h=h,kappa=kappa).items()},endpoint_margin=str(margin),row_extension=str(extension),extended_margin=str(extended_margin),retained_extended_margin=str(margin-2*extension),
        branches=branches,bernstein_conversion_identities_exact=True,auxiliary_checks=checks,row_count_and_slopes=range_certificates(J,RJ,D,P,delta,x,kappa),low_piecewise_range=low_range_certificate(ell),budget_feasibility=budget_feasibility(theta,ell,lx,ly,h,margin,extension,extended_margin),negative_controls=dict(incumbent_margin_fails=dict(delta=str(wd),x=str(wx),weighted_exponent=str(wE),difference_from_old_negative_margin=str(wE+Q(1,10000))),old_geometry_low_bound_misses_target_by=str(low_gap),coverage=coverage_negative_controls()),
        proof_scope='Exact rational scalar inequalities, full branch domains and proposed complete parameter-budget feasibility proved by this audit. The new analytic source cohort and all-family continuation are not validated.',analytic_proof_certified=False,Lean_run=False,kernel_run=False,network_used=False,tracker_commit=PIN,source_evidence_kind='Pinned external maintainer receipt and source-byte comparison; not a local proof replay',script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),input_sha256={SOURCE_INPUT:hashlib.sha256(source_path.read_bytes()).hexdigest()})
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--check',action='store_true',help='Recompute and compare the stored certificate without modifying files')
    mode.add_argument('--write',action='store_true',help='Write the exact certificate after all checks pass')
    args=parser.parse_args()
    result=report()
    if args.write:
        REPORT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        assert json.loads(REPORT.read_text())==result,'Certificate stale; review before using --write'
    print(json.dumps(dict(status=result['status'],target=result['target'],improvement=result['improvement'],branch_rectangles=[b['leaf_count'] for b in result['branches']],auxiliary_checks=len(result['auxiliary_checks']),budget_status=result['budget_feasibility']['status'],analytic_proof_certified=False,Lean_run=False,kernel_run=False),indent=2))


if __name__=='__main__':
    main()
