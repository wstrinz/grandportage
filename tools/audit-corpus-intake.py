import hashlib,json,tempfile
from pathlib import Path
from scripts import corpus_check as C,project_ir_corpus as P
from grandportage import store as S
ROOT=Path(__file__).resolve().parents[1]
work=Path(tempfile.mkdtemp(prefix='intake-boundary-',dir=ROOT/'tmp'));src=work/'source';src.mkdir()
(src/'graph.jsonl').write_text(json.dumps({'ev':'meta','graph_format':8})+'\n'+json.dumps({'ev':'verdict','id':'V','representation':{'proof':1}})+'\n',encoding='utf-8')
corpus=work/'synthetic-corpus'
for name in C.CAMPAIGNS:C.export(src,corpus/name)
intake=C.check(corpus);assert intake['status']=='READY'
rows=[{'name':'structural retention intake accepts unloadable synthetic graph','intake_status':'READY','scope':'READY is retention eligibility, not load-time authority; mirrors retained test fixture'}]
try:P.run_campaign_corpus(corpus,work/'output')
except S.GraphError as e:rows.append({'name':'ready intake then native loading','exception':'GraphError','reason':str(e),'report_written':(work/'output/corpus-report.json').exists()})
else:raise AssertionError('expected native loading refusal')
(src/'export-manifest.json').write_text('{"preexisting":"source artifact"}\n',encoding='utf-8')
C.export(src,work/'reserved-export');result=C.validate_campaign(work/'reserved-export')
assert result['status']=='BLOCKED-ON-CORPUS' and any('SHA mismatch: export-manifest.json' in s for s in result['reasons'])
rows.append({'name':'source already contains export-manifest.json','export_returned_success':True,'validation':result,'scope':'Exporter overwrites copied reserved file with generated metadata; only synthetic files used'})
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Synthetic directories only; no actual campaign harvest.','controls':rows}
(ROOT/'reports/CORPUS-INTAKE-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('3 intake controls verified')
