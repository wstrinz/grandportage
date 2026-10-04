"""Diagnostic deletion controls for the frozen, opt-in coverage inventory."""
import copy,hashlib,importlib.util,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay);replay.validate()
from inventory_probes import observe
base=json.loads((ROOT/'corpus/must/GP-X193.json').read_text(encoding='utf-8'))['inputs']
records=[]
for dimensions,expected in [(['order'],{'order':['-4','0','1','2']}),(['place'],{'place':['t']}),([],{})]:
 d=copy.deepcopy(base);d['asserted_dimensions']=dimensions
 raw=observe(d);assert raw['gaps']==expected
 records.append(dict(asserted_dimensions=dimensions,observation=raw))
report=dict(oracle_commit=replay.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),adapter_sha256=replay.sha(ROOT/'tools/inventory_probes.py'),case_sha256=replay.sha(ROOT/'corpus/must/GP-X193.json'),scope='Diagnostic deletion controls, not approval to remove coverage obligations or proof of model completeness.',records=records,limitation='Only listed dimensions are checked. Declaring an index does not encode or verify strength of its equations. No finding is not evidence of adequate modelling.')
(ROOT/'reports/COVERAGE-BOUNDARY-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Three coverage deletion controls reproduced; removing an axis hides only that axis, and removing both leaves no coverage finding.')
