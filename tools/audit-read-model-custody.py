"""Bounded offline review of presentation size and snapshot path classification."""
from pathlib import Path
import hashlib, importlib.util, json, subprocess, tempfile
ROOT=Path(__file__).resolve().parents[1]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
r=load('replay',ROOT/'tools/check-corpus.py');r.validate()
from grandportage import projection as P
snapshot=load('snapshot',ROOT/'oracle/checkout/scripts/public_snapshot.py')
compact=load('compact',ROOT/'oracle/checkout/scripts/compact_review_projection.py')
with tempfile.TemporaryDirectory(prefix='read-model-',dir=ROOT/'tmp') as directory:
    base=Path(directory);source=base/'source.jsonl';out=base/'output.json'
    source.write_bytes(b'{"id":"R"}\n'*5500)
    value=P.compact_review_projection(source,max_records=5500)
    compact_bytes=len(P.canonical_json(value,pretty=False).encode())
    assert compact.main([str(source),str(out),'--max-records','5500'])==0
    pretty_bytes=out.stat().st_size
    assert compact_bytes<1000000<pretty_bytes,(compact_bytes,pretty_bytes)
    assert json.loads(out.read_text())==value
    assert value['source']['sha256']=='sha256:'+hashlib.sha256(source.read_bytes()).hexdigest()
    assert value['authority']=='DERIVED_READ_MODEL_ONLY' and value['graph_effect']=='NONE'
    size={'records':5500,'compact_bytes':compact_bytes,'actual_cli_bytes':pretty_bytes,'limit':1000000,'source_digest_verified':True,'graph_effect':value['graph_effect']}
    small=base/'small.jsonl';small.write_bytes(b'{"id":"first"}\nnot-json\n{"id":"last"}\n')
    v=P.compact_review_projection(small,max_records=2)
    assert v['selection']=={'rule':'BOUNDED_FIRST_AND_LAST_RECORD_COMMITMENTS','selected':2,'omitted':1,'invalid_json':1}
    small_control=v['selection']
manifest=snapshot.load_manifest(ROOT/'oracle/checkout/public-snapshot-v1.json')
rows=[]
for path,expected in [('experiments/arr15_ranker/adapter.py',False),('experiments/neutral_campaign/adapter.py',True),('fixtures/arr15/new.json',True)]:
    try:
        result=snapshot.classify_paths(manifest,manifest['required_public_paths']+[path])
        observed=path in result['public'];message='classified public'
    except snapshot.PublicSnapshotError as exc:
        observed=False;message=str(exc)
    assert observed is expected,(path,observed)
    rows.append({'path':path,'public':observed,'message':message})
report={'size_control':size,'omitted_invalid_record_control':small_control,'path_controls':rows,'scope':'Synthetic F scratch only; no snapshot materialization, publication, campaign contents, graph mutation or CAS. Path classifications use pinned manifest and synthetic candidate lists.','findings':['CLI output exceeds the advertised 1 MB bound because it serializes pretty JSON after a compact-size check.','Campaign marker detection is lexical; neutral names pass broad public prefixes and existing allowed roots accept new files. This is documented custody policy, not content inspection or secrecy.'],'proposed_fix':'Enforce the byte bound on the actual serialized output, or write exactly the checked compact bytes. Keep path custody rules explicitly distinct from content/security review.','source_hashes':{p:r.sha(ROOT/p) for p in ['oracle/checkout/grandportage/projection.py','oracle/checkout/scripts/compact_review_projection.py','oracle/checkout/scripts/public_snapshot.py','oracle/checkout/public-snapshot-v1.json']},'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'reports/READ-MODEL-CUSTODY-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'size_control':size,'path_controls':len(rows),'omitted_invalid_record_control':small_control}))
