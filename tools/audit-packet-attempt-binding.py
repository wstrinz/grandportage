import copy,hashlib,importlib.util,json,tempfile
from pathlib import Path
from grandportage import campaign as C
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('campaign_tests',ROOT/'oracle/checkout/tests/test_campaign.py')
T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
work=Path(tempfile.mkdtemp(prefix='packet-binding-',dir=ROOT/'tmp'))
packet_path,ledger_path=T._copy_fixture(work)
old_packets=C.build_packets_path(packet_path);old=C.build_ledger_path(ledger_path)
old_fp=old['attempts'][0]['packet_fingerprint']
packet,root=T._manifest_root(packet_path)
catalog_path=root/packet['task_catalog']['path']
catalog=json.loads(catalog_path.read_text(encoding='utf-8'))
catalog['tasks'][0]['statement']['proposition']='Changed obligation under the same packet ID.'
T._write(catalog_path,catalog);T._refresh_packet(packet_path);T._refresh_ledger(packet_path,ledger_path)
new_packets=C.build_packets_path(packet_path);new=C.build_ledger_path(ledger_path)
new_fp=new['attempts'][0]['packet_fingerprint']
assert old_fp!=new_fp and new['attempts'][0]['outcome']=='ACCEPTED_ARTIFACT'
rows=[{'name':'existing attempt input rebound after packet statement change','old_packet_fingerprint':old_fp,'new_packet_fingerprint':new_fp,'outcome':new['attempts'][0]['outcome'],'scope':'Manifest digest bindings explicitly refreshed; no prior_ledger requested; does not bypass file hash checks'}]
overlay=C.build_overlay(new_packets,old)
assert overlay['items'][0]['packet_fingerprint']==new_fp and overlay['items'][0]['outcomes']==['ACCEPTED_ARTIFACT']
rows.append({'name':'old ledger over changed packet with same ID','overlay_packet_fingerprint':new_fp,'ledger_attempt_fingerprint':old_fp,'outcome':overlay['items'][0]['outcomes'][0],'scope':'Direct overlay API accepts mismatching content identities; ordinary CLI rebuilds ledger against current packet'})
prior_path=work/'prior.json';prior_path.write_text(C.canonical_json(old),encoding='utf-8')
v=json.loads(ledger_path.read_text(encoding='utf-8'));v['prior_ledger']={'path':'prior.json','digest_algo':C.DIGEST_ALGO,'sha256':T._digest(prior_path)};T._write(ledger_path,v)
try:C.build_ledger_path(ledger_path)
except C.CampaignError as e:
    assert 'changed or disappeared' in str(e)
    rows.append({'name':'explicit prior ledger blocks rebinding','result':'REFUSED','reason':str(e)})
else:raise AssertionError('prior should protect binding')
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Pinned GP-owned fixture copied to private scratch; no external campaign harvest, verifier execution or graph authority.','controls':rows}
(ROOT/'reports/PACKET-ATTEMPT-BINDING-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('3 packet-attempt binding controls verified')
