"""Bound source identity claims to their cached Git observations."""
from pathlib import Path
import hashlib,importlib.util,json
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import identity as I,format as F,store as S
rows=[]
I.source_identity.cache_clear()
state={'commit':'a'*40,'status':''};calls=[]
def git(root,*args):
 calls.append(list(args));return state['commit'] if args==('rev-parse','HEAD') else state['status']
try:
 with patch.object(I,'source_root',return_value='synthetic-root'),patch.object(I,'_git',side_effect=git):
  first=I.source_identity();state.update(commit='b'*40,status=' M changed.py');cached=I.source_identity();assert first==cached==('a'*40,False);assert len(calls)==2
  I.source_identity.cache_clear();fresh=I.source_identity();assert fresh==('b'*40,True)
  rows.append(dict(id='process_cache',first=first,after_simulated_checkout_change=cached,after_explicit_cache_clear=fresh,git_calls=calls))
 I.source_identity.cache_clear()
 with patch.object(I,'source_root',return_value=None):
  absent=I.source_identity();assert absent==(None,None)
  text=I.version_text(I.implementation_identity('test',8,12));assert 'source unavailable' in text and 'dirty unknown' in text
  rows.append(dict(id='unavailable_source',identity=absent,rendered=text))
finally:I.source_identity.cache_clear()
header=F.meta_event();header['implementation']['source_commit']=123
try:F.validate_meta(header,'synthetic',S.GraphError)
except TypeError as exc:rows.append(dict(id='malformed_commit_type',exception='TypeError',message=str(exc)))
else:raise AssertionError('Expected unnormalized metadata type error')
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/identity.py','grandportage/format.py']},'interpretation':['Git identity is a process-cached observation, not a digest of loaded code or a continuously refreshed checkout attestation. Simulated changes are observed only after cache clear.','Unavailable Git context remains explicitly unknown; no commit or clean flag is fabricated.','JSON numeric source_commit raises raw TypeError in regex validation instead of GraphError; malformed input is not accepted, but domain error normalization is incomplete.'],'proposed_fix':'Describe identity as cached source metadata; if stronger reproducibility is needed, bind release/content digests at build time. Validate source_commit type before regex matching and return the declared domain error. Do not infer executable authenticity from a self-reported identity.','scope':'Mocked Git observations and one malformed metadata scalar; no checkout mutation or false mathematical authority.'}
(ROOT/'reports/IMPLEMENTATION-IDENTITY-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Three identity boundary controls verified.')
