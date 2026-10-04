"""Offline launch/recording boundary probes with a counted injected runner."""
from pathlib import Path
from tempfile import TemporaryDirectory
from grandportage import cas,store as S,artifacts as A
ROOT=Path(__file__).resolve().parents[1]
def probe(case,route):
 d=case['inputs'];mode=d['declaration'];outcome=d['process_outcome']
 if mode not in {'omitted','unknown_relation','untyped_without_reason','untyped_with_reason','typed','missing_source'} or outcome not in {'success','reported_error','nonzero_exit','aborted'}:raise ValueError('Unsupported launch scenario')
 if d['request_form'] not in {'structured','raw_text'}:raise ValueError('Unsupported request form')
 with TemporaryDirectory(prefix='launch-probe-',dir=ROOT/'tmp') as root:
  S.append([dict(ev='model',id='SRC',desc='source',field='Q')],root)
  path=Path(S.graph_path(root));before=path.read_bytes();calls=[]
  def runner(p,t):
   calls.append('called');stdout='@@GP_I:\n1\n'
   if outcome=='reported_error':stdout='? error occurred\n'+stdout
   rc={'success':0,'reported_error':0,'nonzero_exit':1,'aborted':124}[outcome]
   return dict(returncode=rc,stdout=stdout+p.completion_marker+'\n',stderr='',aborted=outcome=='aborted',abort_reason='timeout' if outcome=='aborted' else None,argv=['offline-spy'])
  program=cas.CASProgram(cas.SINGULAR,ring='GP_R',ring_vars=['x'],decls=[('GP_I','ideal','x')],body=[],outputs=['GP_I']) if d['request_form']=='structured' else 'ideal I=x;'
  relation={'src':'MISSING' if mode=='missing_source' else 'SRC','type':'UNTYPED' if mode.startswith('untyped') else 'PROBABLY_FINE' if mode=='unknown_relation' else 'IMAGE_CLOSURE','why':'declared operation','map_kind':'POLYNOMIAL'}
  if mode=='untyped_with_reason':relation['debt_why']='relation not yet established'
  kwargs=dict(produces='RESULT',describes='computed output',root=root,_runner=runner)
  if mode!='omitted':kwargs['edge']=relation
  error=None;result=None
  try:result=cas.run_cas(program,**kwargs)
  except (TypeError,cas.CASError,S.GraphError) as exc:error=str(exc)
  graph=S.load(str(path));created='RESULT' in graph.models
  audit=A.audit_graph_report(root,graph)
  return dict(observed_verdict='ACCEPT' if error is None and result['verdict']=='OK' and created else 'REFUSE',reason=error or ('Completed declaration/recording control only, no theorem authority.' if created else 'An aborted attempt creates no model.'),runner_calls=len(calls),graph_bytes_unchanged=path.read_bytes()==before,created_model=created,edge_ids=sorted(graph.edges),note_kinds=[n.get('kind') for n in graph.notes],artifact_files=len(list((Path(root)/'.portage/artifacts').rglob('*.json'))),artifact_audit=audit,execution_descriptor='counted_injected_runner_no_external_process')
