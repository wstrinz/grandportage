import hashlib,importlib.util,json
from pathlib import Path
from grandportage import explain as E
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('project_tests',ROOT/'oracle/checkout/tests/test_project_v2.py');T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
g=T.graph()
g.apply({'ev':'inference','id':'I','premises':[{'claim':'C','path':[]}],'concludes_kind':'EMPTY','asserted':'transport only'})
g.validate()
report=E.explain(g,'I')
assert report['tree']['complete'] is False
assert report['tree']['children'][0]['runtime_licensed'] is False
assert report['tree']['lost']['profile_covered'] is True
out={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Native validated graph, no verifier receipt; zero-step transport profile is separate from earned premise authority.','report':report}
(ROOT/'reports/EXPLAIN-TRANSPORT-BOUNDARY.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'complete':report['tree']['complete'],'runtime_licensed':report['tree']['runtime_licensed'],'profile_covered':report['tree']['lost']['profile_covered'],'child_runtime_licensed':report['tree']['children'][0]['runtime_licensed']}))
