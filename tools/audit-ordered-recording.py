"""Replay canonical and equivalent noncanonical SOS model presentations."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import format as F, store as S, verify as V, provenance as P
rows=[]
for expression in ['x^2+1','x*x+1']:
 graph=S.Graph();graph.apply(F.meta_event())
 graph.apply({'ev':'model','id':'M','about':'ANY_ORDERED','compute_in':'Q','coefficient_domain':'Q','characteristic':0,'point_universe':'BASE','ring_vars':['x'],'generators':[expression]})
 graph.apply({'ev':'claim','id':'E','model':'M','kind':'EMPTY','statement':'no ordered-field zero','certificate':'ORDERED_SOS_CERT','scope':'ANY_ORDERED'})
 cert={'method':'rational_sos_cofactor_v1','ring_vars':['x'],'generators':[expression],'squares':['x'],'cofactors':['-1']}
 verdict,why,rep=V.ordered_sos(graph,'E',cert);assert verdict==V.CERT_VERIFIED
 event=V._verdict_event(graph,'certificate','E',verdict,why,rep,execution=P.native_execution_provenance())
 try:graph.apply(event);accepted=True;error=None
 except S.GraphError as exc:accepted=False;error=str(exc)
 assert accepted==(expression=='x^2+1')
 rows.append({'input_generator':expression,'verifier_verdict':verdict,'normalized_representation':rep,'fold_accepted':accepted,'fold_error':error,'certificate_reach':graph.claims['E'].get('certificate_reach')})
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/ordered_sos.py','grandportage/store.py','grandportage/verify.py']},'finding':'The verifier accepts an exact proof bound to x*x+1 and emits canonical x^2+1; fold replay compares that canonical generator text against the original model text and rejects. Canonical input records successfully. This is a conservative producer/consumer representation mismatch, not false authority.','proposed_fix':'Separate raw model binding from canonical arithmetic representation, or compare validated canonical forms consistently while retaining the original input fingerprint. Preserve rejection of genuinely changed generators.','scope':'Two native, current-metadata controls; no backend, campaign data or oracle modifications.'}
(ROOT/'reports/ORDERED-SOS-RECORDING-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Two SOS producer/fold controls verified.')
