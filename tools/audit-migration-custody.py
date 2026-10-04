"""Bounded migration header custody and dropped partition-field controls."""
from pathlib import Path
import copy,hashlib,importlib.util,json,tempfile
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import format as F,migration as M,store as S
rows=[]
with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='migration-audit-') as tmp:
 for name,fmt,identity in [('historical_missing_identity',6,False),('current_format_old_epoch_missing_identity',F.GRAPH_FORMAT,False),('current_format_old_epoch_valid_identity',F.GRAPH_FORMAT,True)]:
  header=F.meta_event();header['graph_format']=fmt;header['kernel_epoch']=F.KERNEL_EPOCH-1
  if identity:header['implementation'].update(graph_format=fmt,kernel_epoch=F.KERNEL_EPOCH-1)
  else:header.pop('implementation')
  source=Path(tmp)/(name+'.jsonl');source.write_text(json.dumps(header)+'\n',encoding='utf-8');before=source.read_bytes()
  try:report=M.migrate_kernel_epoch([str(source)],dry_run=True);accepted=True;error=None
  except S.GraphError as exc:accepted=False;error=str(exc)
  assert accepted==(fmt==F.GRAPH_FORMAT)
  assert source.read_bytes()==before
  rows.append(dict(id=name,accepted=accepted,error=error,source_sha256=hashlib.sha256(before).hexdigest(),source_unchanged=True,dry_run=True))
 events=[dict(ev='model',id=x) for x in ['M','A','B']]+[dict(ev='claim',id='COVER',model='M',kind='PREDICATE',statement='cover'),dict(ev='partition',id='P',parent='M',branches=['A','B'],exhaustive='COVER',why='split')]+[dict(ev='claim',id='E'+x,model=x,kind='EMPTY',statement='empty',certificate='UNIT_IDEAL_CERT') for x in ['A','B']]+[dict(ev='inference',id='JOIN',via_partition='P',premises=[{'claim':x} for x in ['EA','EB','COVER']],concludes_kind='EMPTY',asserted='parent empty')]
 source=Path(tmp)/'partition.jsonl';source.write_text(''.join(json.dumps(x)+'\n' for x in events),encoding='utf-8');before=source.read_bytes();S.load(str(source))
 converted,actions=M._native_record(events[-1],'sha256:'+hashlib.sha256(before).hexdigest());assert 'via_partition' not in converted
 try:M.migrate_epoch1([str(source)],dry_run=True)
 except S.GraphError as exc:error=str(exc);assert 'premises do not meet' in error
 else:raise AssertionError('partition migration unexpectedly succeeded')
 assert source.read_bytes()==before
 rows.append(dict(id='legacy_partition_migration',accepted=False,error=error,conversion_actions=actions,source_unchanged=True,dry_run=True))
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/format.py','grandportage/migration.py']},'findings':['Historical format missing identity refuses, but current-format/older-epoch missing identity passes migration dry-run because header validation is skipped on that branch. New output header would describe the current writer; malformed source custody is not independently validated.','Legacy partition conversion drops via_partition, then strict graph validation rejects noncolocated premises. It does not make the legacy case split native.'],'proposed_fix':'Validate current-format/older-epoch source header shape and internal identity consistency under its recorded epoch before replacing it. Keep arithmetic authority/replay separate. Handle unsupported semantic fields through explicit refusal or approved conversion, not silent rule erasure.','scope':'Three header controls and one partition migration; dry-run only, original bytes unchanged, no old campaign files read or modified.'}
(ROOT/'reports/MIGRATION-CUSTODY-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Four migration custody controls verified.')
