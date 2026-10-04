"""Calibrate structural adapter conformance without treating it as checker admission."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay);replay.validate()
from grandportage import adapter_conformance as C
from tests.test_adapter_conformance import _adapter
records=[]
for mode in ['matching','incorrect_cofactor_self_report','declared_effect_self_report']:
 adapter=_adapter();envelope=adapter.build_envelope()
 if mode=='incorrect_cofactor_self_report':envelope['certificate_payload']['cofactors']=['0'];adapter.replay=lambda _v:{'verified':True}
 if mode=='declared_effect_self_report':adapter.GRAPH_EFFECT='LOCAL_EMPTY';envelope['graph_effect']='LOCAL_EMPTY'
 report=C.check_adapter(adapter);assert report['status']=='CONFORMING' and report['authority']=='DESCRIPTIVE_ONLY'
 records.append(dict(mode=mode,report=report))
result=dict(oracle_commit=replay.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records,scope='Diagnostic structural-harness controls. No graph event, source file mutation or external adapter execution.',finding='Conformance trusts adapter replay and declared effect, and lists mutation names without running mutations. A wrong certificate can self-report verified and remain DESCRIPTIVE_ONLY; this is not evidence of a held false claim.')
(ROOT/'reports/ADAPTER-CONFORMANCE-BOUNDARY.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Three conformance boundary controls reproduced; none grants proof authority.')
