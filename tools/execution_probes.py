"""Offline execution-envelope probes; fabricated transcripts never mint graph authority."""
from unittest.mock import patch
from grandportage import cas
BANNER='Singular for x86_64-Linux version 4.2.1 (4212, 64 bit)'
def program():return cas.CASProgram(cas.SINGULAR,ring='GP_R',ring_vars=['x'],decls=[('GP_G','ideal','std(ideal(x))')],body=[],outputs=['GP_G'],characteristic=0)
def raw(s):return dict(returncode=0,stdout=s,stderr='',aborted=False,abort_reason=None,argv=['offline-test-double'])
def finished(p,s):return s+p.completion_marker+'\n'
def probe(case,route):
 d=case['inputs'];mode=d['variation'];b=None;error=None;parsed=None
 if d['request'] != dict(coefficient_field='Q',variables=['x'],ideal_generators=['x'],operation='basis'):raise ValueError('This bounded envelope probe supports only the declared Q[x] basis request')
 allowed={'identity':{'matching','different_version','absent_identity','repeated_identity','foreign_invocation'},'completion':{'matching','absent_completion','foreign_invocation','repeated_completion','trailing_output'}}
 if mode not in allowed.get(d['boundary'],set()):raise ValueError('Unknown envelope variation')
 if d['evidence_origin']!='fabricated_offline_control':raise ValueError('Only explicit offline controls are supported')
 if d['boundary']=='identity':
  def runner(p,t):
   n=p.completion_nonce;nonce='0'*32 if mode=='foreign_invocation' else n
   banner=BANNER.replace('4.2.1','4.3.1') if mode=='different_version' else BANNER
   identity='@@GP-ID:'+nonce+'\n'+banner+'\n@@GP-ID-END:'+nonce+'\n'
   if mode=='absent_identity':identity=''
   if mode=='repeated_identity':identity+=identity
   return raw(finished(p,identity+'@@GP_G:\nGP_G[1]=x\n'))
  with patch.object(cas,'_singular_binary_version',return_value=BANNER),patch.object(cas,'_run_subprocess',side_effect=runner):
   b=cas.SingularBackend()
   try:
    run=b.execute(program());parsed=cas._parse_result(run,['GP_G']);accepted=b.can_record_verdicts
   except cas.CASError as exc:error=str(exc);accepted=False
   flag=b.can_record_verdicts
   try:provenance=b.provenance();aggregate=True
   except cas.CASError:aggregate=False
  return dict(observed_verdict='ACCEPT' if accepted else 'REFUSE',reason=error or 'Fabricated matching identity envelope accepted by isolated control flow only.',boundary='in_band_identity',recording_flag_under_test_double=flag,aggregate_identity_consistent=aggregate,retained_executions=len(b.executions),parsed=parsed,execution_descriptor='fabricated_transcript_no_external_process',graph_effect='NONE')
 if d['boundary']!='completion':raise ValueError('Unknown boundary')
 def runner(p,t):
  prefix='@@GP_G:\nGP_G[1]=x\n'
  if mode=='absent_completion':return raw(prefix)
  if mode=='foreign_invocation':return raw(prefix+'@@GP-END:'+'0'*32+'\n')
  text=finished(p,prefix)
  if mode=='repeated_completion':text+=p.completion_marker+'\n'
  if mode=='trailing_output':text+='a second transcript\n'
  return raw(text)
 b=cas.SingularBackend(runner=runner,binary_version='test')
 run=b.execute(program())
 try:parsed=cas._parse_result(run,['GP_G']);accepted=True
 except cas.CASError as exc:error=str(exc);accepted=False
 return dict(observed_verdict='ACCEPT' if accepted else 'REFUSE',reason=error or 'Fabricated complete result envelope parsed; no native backend or graph authority.',boundary='completion_marker',parsed=parsed,frozen_parse_present=run.artifact.parsed_output is not None,execution_descriptor='fabricated_transcript_no_external_process',graph_effect='NONE')
