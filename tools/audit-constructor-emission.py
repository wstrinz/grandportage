"""Offline constructor emission audit; this deliberately does not invoke Singular."""
import hashlib, json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'oracle/checkout'))
from grandportage import operations as O

def main():
    operations=[O.saturate_closure('M','x','SAT',['x','y'],['x*y']),
                O.localize('M','a','OPEN',['a','b'],[]),
                O.saturate_closure('M','a','SAT0',['a','b'],[]),
                O.eliminate('M',['b'],'ELIM0',['a','b'],[])]
    rows=[]
    for op in operations:
        text=op.program.text
        checks={'no_empty_ideal_declaration':'ideal GP_I = ;' not in text,
                'no_unavailable_sat_call':'sat(' not in text,
                'no_library_load':'LIB ' not in text}
        if op.kind=='SaturateClosure':
            checks['rabinowitsch_elimination']='1-GP_T*(' in text and 'eliminate(GP_I,GP_T)' in text
        assert all(checks.values()),checks
        rows.append(dict(kind=op.kind,program=text,checks=checks,events=op.events))
    report=dict(oracle_commit=json.loads((ROOT/'oracle/PIN.json').read_text(encoding='utf-8-sig'))['commit'],
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                layer='constructor_emission_only',external_execution=False,
                limitation='Text inspection does not establish Singular execution or mathematical completeness. Original live constructor regressions remain unrun.',results=rows)
    (ROOT/'reports/CONSTRUCTOR-EMISSION-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Four constructor emission controls passed; no external execution.')
if __name__=='__main__':main()
