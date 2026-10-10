#!/usr/bin/env python3
"""Regenerate exact coefficient literals while preserving compressed Lean proofs.

This only discovers arithmetic coefficients. Its output must be checked by Lean
with geometry based on the requested parameter. It does not prove nonvanishing.
"""
from certificate_model import *
from pathlib import Path
import argparse,json,re,hashlib


def lean_fraction(q):return f'{q.numerator} / {q.denominator}'

def coefficients(cert):
    values=[cert['Av'],cert['Dv'],cert['dv']]
    values += [v for row in cert['shift'] for v in row]
    values += [v-BERNSTEIN_FLOOR for matrix in cert['bernstein'] for row in matrix for v in row]
    return values


def update(source,new_theta,parameter_name='tightTheta',margin=F_MARGIN,
           old_theta=ORIGINAL_THETA,source_parameter_name='theta',old_margin=F_MARGIN):
    original=certificate(old_theta);target=certificate(new_theta)
    checks=validate(target,margin)
    if not all(checks.values()):raise ValueError(f'Certificate arithmetic check failed: {checks}')
    pairs={}
    for old,new in zip(coefficients(original),coefficients(target),strict=True):
        if old in pairs:assert pairs[old]==new
        pairs[old]=new
    replacements=[]
    # One simultaneous substitution avoids interactions among large rationals.
    alternatives={lean_fraction(old):lean_fraction(new) for old,new in pairs.items()}
    pattern=re.compile(r'(?<![0-9])(?:'+'|'.join(re.escape(x) for x in sorted(alternatives,key=len,reverse=True))+r')(?![0-9])')
    seen={old:0 for old in alternatives}
    def replace(match):
        old=match.group();seen[old]+=1
        return alternatives[old]
    result=pattern.sub(replace,source)
    missing=[old for old,n in seen.items() if not n]
    if missing:raise ValueError(f'Input is not the expected current compressed certificate; missing literals: {missing}')
    replacements=[{'old':old,'new':alternatives[old],'occurrences':n} for old,n in seen.items()]
    if margin!=old_margin:
        # The endpoint proof uses J <= 5/2, so E's saving is 2/5 of F's.
        budget_map={old_margin:margin,Q(2,5)*old_margin:Q(2,5)*margin}
        budget_seen={value:0 for value in budget_map}
        def replace_budget(match):
            value=Q(int(match[1]),int(match[2]))
            if value not in budget_map:return match.group()
            budget_seen[value]+=1
            return lean_fraction(budget_map[value])
        result=re.sub(r'(?<![0-9])([0-9]+)\s*/\s*([0-9]+)(?![0-9])',replace_budget,result)
        assert all(budget_seen.values()),budget_seen
        replacements += [{'old':str(old),'new':str(new),'occurrences':budget_seen[old],
                          'kind':'exact rational budget'} for old,new in budget_map.items()]
    if parameter_name!=source_parameter_name:
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',parameter_name):raise ValueError('Invalid Lean parameter name')
        result=re.sub(r'\b'+re.escape(source_parameter_name)+r'\b',parameter_name,result)
    # With the existing margins, prove textually that no proof script has changed:
    # reverse just the coefficient literals and the selected parameter spelling.
    if margin==old_margin:
        reverse={new:old for old,new in alternatives.items()}
        assert len(reverse)==len(alternatives)
        restore_pattern=re.compile(r'(?<![0-9])(?:'+'|'.join(re.escape(x) for x in sorted(reverse,key=len,reverse=True))+r')(?![0-9])')
        restored=restore_pattern.sub(lambda m:reverse[m.group()],result)
        if parameter_name!=source_parameter_name:restored=re.sub(r'\b'+re.escape(parameter_name)+r'\b',source_parameter_name,restored)
        assert restored==source,'Unexpected change outside coefficients/parameter spelling'
    metadata={'original_theta':str(ORIGINAL_THETA),'source_theta':str(old_theta),'theta':str(new_theta),'improvement':str(ORIGINAL_THETA-new_theta),'parameter_name':parameter_name,'F_margin':str(margin),'E_margin':str(Q(2,5)*margin),'Dv':str(target['Dv']),'checks':checks,'replacements':replacements,'proof_scripts_preserved':margin==old_margin,'only_coefficients_budgets_and_parameter_changed':True,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'output_sha256':hashlib.sha256(result.encode()).hexdigest(),'status':'Exact coefficient discovery only; Lean and full analytic validation required.'}
    return result,metadata


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--numerator',type=int,required=True)
    parser.add_argument('--denominator',type=int,required=True)
    parser.add_argument('--source',type=Path,required=True,help='Certificate source with known original coefficients')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'generated/Certificate.lean')
    parser.add_argument('--report',type=Path,help='Metadata JSON (default: output with .json suffix)')
    parser.add_argument('--parameter-name',default='tightTheta')
    parser.add_argument('--f-margin',type=Q,default=F_MARGIN)
    parser.add_argument('--source-theta',type=Q,default=ORIGINAL_THETA)
    parser.add_argument('--source-parameter-name',default='theta')
    parser.add_argument('--source-f-margin',type=Q,default=F_MARGIN)
    args=parser.parse_args()
    if args.denominator<=0:parser.error('denominator must be positive')
    theta=Q(args.numerator,args.denominator)
    if not theta<ORIGINAL_THETA:parser.error('candidate must be strictly tighter than the original')
    result,metadata=update(args.source.read_text(),theta,args.parameter_name,args.f_margin,
        args.source_theta,args.source_parameter_name,args.source_f_margin)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(result)
    report=args.report or args.output.with_suffix('.json')
    report.parent.mkdir(parents=True,exist_ok=True)
    report.write_text(json.dumps(metadata,indent=2)+'\n')
    print('Wrote',args.output,'at theta',theta)
    print('Replaced',len(metadata['replacements']),'distinct coefficient literals; compressed proof scripts preserved:',metadata['proof_scripts_preserved'])
    print('Exact Dv:',metadata['Dv'])

if __name__=='__main__':main()
