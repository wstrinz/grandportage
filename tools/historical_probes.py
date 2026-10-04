"""Layer-specific probes of verbatim GP history; no new kernel authority."""
import copy,gzip,hashlib,importlib.util,json,sys,tempfile,os
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
H=ROOT/'oracle/history/checkout'
MODULES={
 'ladder':'jc_h3_source_ladder/authority_adapter.py',
 'boundary':'jc_h3_source_depth6/adapter.py',
 'chain':'jc_h3_source_depth6/chain_adapter.py',
 'face':'jc_h3_source_depth6/face_extraction_adapter.py',
 'support':'jc_h3_source_depth6/support_seam_handback_adapter.py',
 'closeout':'jc_h3_source_depth6/c710_all_j_closeout_handback_adapter.py',
 'first_value':'jc_h3_source_depth6/source_target_first_value_handback_adapter.py',
 's2':'jc_h3_source_depth6/s2_lowjet_guard_peel_handback_adapter.py',
 's4':'jc_h3_s4_scope/adapter.py',
 'recurrence':'jc_h3_adjoint_recurrence/adapter.py',
 'fiber':'jc_h3_depth8_fiber/adapter.py',
}
def load(name):
 spec=importlib.util.spec_from_file_location('historical_review_'+name,H/'experiments'/MODULES[name])
 module=importlib.util.module_from_spec(spec);sys.modules[spec.name]=module;spec.loader.exec_module(module);return module

def decision(ok,reason,**extra):
 return dict(observed_verdict='ACCEPT' if ok else 'REFUSE',reason=str(reason),**extra)
def no_backend(*a,**k):raise RuntimeError('Historical probe unexpectedly requested a backend')
def mutate(value,operations):
 for op in operations:
  current=value
  for key in op['path'][:-1]:current=current[key]
  key=op['path'][-1]
  if op['op']=='set':current[key]=op['value']
  elif op['op']=='remove':current[key].remove(op['value'])
  else:raise ValueError('Unsupported mutation operation')

def probe(case,route):
 from grandportage import verify as V,store as S,format as F
 historical=json.loads((ROOT/'oracle/history/PIN.json').read_text(encoding='utf-8'))
 if route['historical_commit']!=historical['commit']:raise ValueError('Wrong historical revision')
 d=case['inputs'];family=route['family'];action=route['action']
 if family=='bundle':
  from grandportage import frontier_bundle as B
  value=json.loads((H/'fixtures/frontier/current_v1.json').read_text(encoding='utf-8'))
  if action=='omit_resolution':value['resolutions']=[]
  elif action=='wrong_scope':value['resolutions'][0]['scope_id']=d['proposed_scope']
  elif action!='retain':raise ValueError('Unknown bundle action')
  with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='bundle-probe-') as tmp:
   value['root']=os.path.relpath(H,tmp)
   path=Path(tmp)/'manifest.json';path.write_text(json.dumps(value),encoding='utf-8')
   try:report=B.build_path(path)
   except B.FrontierBundleError as exc:return decision(False,exc,graph_effect='NONE')
  return decision(True,'Explicit receipt overlap resolutions validated.',counts=report['counts'],graph_effect=report['graph_effect'])
 if family in ('ring_observation','affine_block','pointwise','cancellation'):
  from grandportage import groebner as G
  variables=d['variables']
  if family=='ring_observation':
   product='('+d['element']+')*('+d['annihilator']+')'
   receipt=G.check_membership_identity(product,d['generators'],d['cofactors'],variables,0)
   images={name:str(value) for name,value in d['nonzero_point'].items()}
   other={name:str(value) for name,value in d['zero_point'].items()}
   nonzero=G.substitute_polynomial(d['element'],variables,images,0)
   zero=G.substitute_polynomial(d['element'],variables,other,0)
   annihilator=G.substitute_polynomial(d['annihilator'],variables,other,0)
   residuals=[G.substitute_polynomial(g,variables,pt,0) for pt in (images,other) for g in d['generators']]
   if nonzero=='0' or zero!='0' or annihilator=='0' or any(r!='0' for r in residuals):
    raise ValueError('Invalid ring-observation counterexample')
   return decision(action=='nonzero_nonunit','Exact evaluations prove nonzero and nonunit; the displayed nonzero annihilator disproves nonzerodivisor.',zero_product=receipt,nonzero_image=nonzero,zero_image=zero,annihilator_image=annihilator)
  if family=='affine_block':
   if action=='incompatible':
    receipt=G.check_membership_identity('1',d['equations'],d['cofactors'],variables,0)
    return decision(False,'The rank-two block has an incompatible right-hand side; its equations generate one.',unit_receipt=receipt)
   residuals=[G.substitute_polynomial(eq,variables,d['point'],0) for eq in d['equations']]
   return decision(all(r=='0' for r in residuals),'The compatible right-hand side has the displayed exact solution.',residuals=residuals)
  if family=='cancellation':
   product=G.substitute_polynomial(d['product'],variables,d['point'],0)
   cancelled=G.substitute_polynomial(d['cancelled_conclusion'],variables,d['point'],0)
   if product!='0' or cancelled=='0':raise ValueError('Invalid cancellation counterexample')
   return decision(False,'The displayed point satisfies the product equation but not the cancelled equation; the cancelled factor was not a unit.',product_value=product,cancelled_value=cancelled)
  images={**{v:v for v in variables},**d['excluded_base']}
  specialized=[G.substitute_polynomial(eq,variables,images,0) for eq in d['parent_equations']]
  if specialized!=d['excluded_fiber_generators']:raise ValueError('Excluded fiber is not the declared specialization')
  unit=G.check_membership_identity('1',d['excluded_fiber_generators'],['1'],['x'],0)
  residuals=[G.substitute_polynomial(eq,variables,d['parent_point'],0) for eq in d['parent_equations']]
  if any(r!='0' for r in residuals):raise ValueError('Invalid parent witness')
  return decision(False,'One fiber is empty, but the displayed point lies over another base value.',fiber_unit=unit,parent_residuals=residuals)
 m=load(family)
 if family=='ladder':
  value=copy.deepcopy(d['chain'])
  if action=='bad_solution':value['steps'][2]['solution']='0'
  try:graph,compiled=m.graph_from_spec(value)
  except ValueError as exc:
   if action!='bad_solution':raise
   return decision(False,exc,refused_at='ordered_chain_replay')
  if action=='bad_cofactor':graph.edges[compiled['edge_id']]['ring_iso_certificate']['forward_cofactors'][1][0]='0'
  elif action=='missing_inverse':graph.models[compiled['source_model']]['generators'].pop()
  elif action not in ('retain','bad_solution'):raise ValueError('Unknown ladder action')
  verdict,why=V.ring_iso(graph,compiled['edge_id'],_runner=no_backend)
  return decision(verdict==V.ISO_VERIFIED,why,raw_verdict=verdict,inverse_variables=compiled['inverse_variables'],inverse_witnesses=compiled['inverse_witnesses'])
 if family=='boundary':
  frozen=json.loads(m.DEFAULT_FROZEN.read_text(encoding='utf-8'))
  if action=='promote_digest':
   frozen['source_binding']='CHECKED_ACTUAL_SOURCE_DERIVATION'
   try:m.verify_frozen(frozen)
   except m.Depth6ReceiptError as exc:return decision(False,exc,graph_effect='NONE')
   return decision(True,'Source-binding upgrade accepted.')
  graph=m.graph_from_frozen(frozen)
  if action=='source_edge':
   edges=[e['id'] for e in graph.edges.values() if m.BOUNDARY_MODEL in (e['src'],e['dst'])]
   return decision(bool(edges),'No actual-source or parent-cover edge is supplied by the frozen boundary.',incident_edges=edges,claim_count=len(graph.claims))
  edge=m.DISCRIMINANT_EDGE if action=='discriminant' else m.GENERIC_EDGE
  if action=='missing_inverse':graph.models[m.GENERIC_MODEL]['generators'].pop()
  elif action=='bad_cofactor':graph.edges[edge]['ring_iso_certificate']['forward_cofactors'][3][3]='GP_INV_alpha+1'
  elif action not in ('generic','discriminant'):raise ValueError('Unknown boundary action')
  verdict,why=V.ring_iso(graph,edge,_runner=no_backend)
  return decision(verdict==V.ISO_VERIFIED,why,raw_verdict=verdict,source_binding=frozen['source_binding'])
 if family=='chain':
  if action=='preflight':
   report=m.preflight_chain()
   return decision('chain identity authority' not in report['refuses'],'Preflight licenses only named-input bindings.',raw_verdict=report['verdict'],licenses=report['licenses'],refuses=report['refuses'])
  value=json.loads(gzip.decompress(m.DEFAULT_FROZEN.read_bytes()))
  if action=='reorder':value['steps'][0],value['steps'][1]=value['steps'][1],value['steps'][0]
  elif action=='bad_unit':
   term=value['steps'][0]['pivot_inverse']['terms'][0];term[1]=str(m.Q(term[1])*2)
  elif action=='bad_value':
   term=value['steps'][0]['value']['sparse']['terms'][0];term[1]=str(m.Q(term[1])+1)
  elif action=='drop_refusal':value['refusals'].remove('H3 promotion')
  elif action!='retain':raise ValueError('Unknown chain action')
  # Match the historical mutation assays: only scratch outer hashes are repinned
  # so ordered-state, unit identity and inner commitment checks are reached.
  canonical=json.dumps(value,separators=(',',':')).encode();compressed=gzip.compress(canonical,mtime=0)
  m.EXPECTED_CANONICAL_SHA256=hashlib.sha256(canonical).hexdigest();m.EXPECTED_COMPRESSED_SHA256=hashlib.sha256(compressed).hexdigest()
  with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='chain-probe-') as tmp:
   path=Path(tmp)/'chain.json.gz';path.write_bytes(compressed)
   try:report=m.verify_chain(path)
   except m.Depth6ChainError as exc:return decision(False,exc,full_face_substitution_replayed=False)
  return decision(True,'Ordered reduced equations, unit identities and endpoint bindings replayed.',raw_verdict=report['verdict'],solved_steps=report['solved_steps'],full_face_substitution_replayed=False)
 if family=='face':
  value=json.loads(m.DEFAULT_FIXTURE.read_text(encoding='utf-8'))
  if action=='row':
   record=value['source_rows'][0];term=record['sparse']['terms'][0];term[1]=str(m.Q(term[1])+1);record['sha256']=m.CHAIN._sparse_digest(record['sparse'])
  elif action=='support':value['root_supports']['2'][0]+=1
  elif action=='series':value['coordinate_series']['7'][0]='c7_10'
  elif action=='formula':value['formula']['p_side_rows']=13
  elif action=='output':value['output_faces'][0]['sha256']='0'*64
  elif action=='budget':
   class ZeroBudget(m._Budget):
    def __init__(self):super().__init__(max_products=0)
   m._Budget=ZeroBudget
  elif action!='retain':raise ValueError('Unknown face action')
  raw=(json.dumps(value,indent=2,sort_keys=True,ensure_ascii=True)+'\n').encode();m.EXPECTED_FIXTURE_SHA256=hashlib.sha256(raw).hexdigest()
  with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='face-probe-') as tmp:
   path=Path(tmp)/'face.json';path.write_bytes(raw)
   try:report=m.verify_fixture(path)
   except m.FaceExtractionError as exc:return decision(False,exc,mathematical_refutation=False)
  return decision(True,'Exact graded face extraction replayed under the declared finite supports.',raw_verdict=report['verdict'],faces=report['faces'],graph_effect='NONE')
 # Contract probes call the historical validator, never a stored test verdict.
 # Full native fixtures remain hash-bound oracle inputs; neutral cases carry
 # the relevant scope contract and the proposed change.
 handback=family in ('support','closeout','first_value','s2')
 value=m.load_fixture() if handback else json.loads(m.DEFAULT_FIXTURE.read_text(encoding='utf-8'))
 validator=m.validate_handback_value if handback else m.validate_fixture_value
 section=d['contract_section']
 if value[section]!=d['baseline_contract']:raise ValueError('Neutral contract differs from historical input')
 validator(copy.deepcopy(value))
 mutate(value,d.get('operations',[]))
 try:checked=validator(value)
 except ValueError as exc:
  if not str(exc).startswith(tuple(route.get('failure_prefixes',[]))):raise
  return decision(False,exc,graph_effect='NONE',layer_limit=route['layer'])
 if family=='s4' and action=='point':
  return decision(True,'Exact K-valued point substitution and nonzero guards replayed.',graph_effect='NONE',point=value['native_receipt']['point'])
 if family=='recurrence' and action=='tail':
  return decision(True,'Finite operator tail and nonzero endpoint checked; generic theorem not recompiled.',checked_premises=checked[1],graph_effect='NONE')
 return decision(True,'Historical scope contract retained; stated external premises remain undischarged.',graph_effect='NONE')
