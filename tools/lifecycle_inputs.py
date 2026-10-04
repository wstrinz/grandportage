"""Translate portable lifecycle scenarios into the frozen GP oracle vocabulary.

This is corpus adapter code, not the 0.50 fold or a proof checker.
"""
import copy
VOCABULARY='lifecycle-scenario/v1'
ENTITIES={'context':'model','assertion':'claim','relation':'edge','argument':'inference'}
ATTRIBUTES={'description':'desc','context':'model','statement':'statement','citation':'cite','source_context':'src','target_context':'dst','justification':'why','unresolved_reason':'debt_why','premise':'claim','conclusion':'asserted','coefficients_from_base':'coefficients_in_base'}
ENUMS={
 'statement_class':('kind',{'universal_property':'PREDICATE','polynomial_identity':'IDENTITY'}),
 'conclusion_class':('concludes_kind',{'universal_property':'PREDICATE','polynomial_identity':'IDENTITY'}),
 'relation_class':('type',{'unspecified':'UNTYPED','equations_forgotten':'NECESSARY_CONDITION','subset_restriction':'RESTRICTION'}),
 'coordinate_action':('map_kind',{'unchanged':'IDENTITY_MAP'}),
 'identity_basis':('identity_origin',{'context_equations':'DERIVED'})}
CHANGES={'annotation_only':'AMEND','restatement':'RESTATE','relation_reclassification':'RETYPE','argument_retraction':'RETRACT','relation_withdrawal':'WITHDRAW'}
CONCERNS={'unresolved_relation':'UNTYPED-EDGE','competing_relations':'PARALLEL-EDGE','retired_route_dependency':'STALE-PATH','retired_context_dependency':'STALE-MODEL'}

def keys(value,allowed,required=()):
    if not isinstance(value,dict) or set(value)-set(allowed) or set(required)-set(value):
        raise ValueError('Invalid lifecycle object fields: '+repr(value))

def decode(data):
    keys(data,{'vocabulary','objects','history','branch_comparison','question'},{'vocabulary','objects','history','question'})
    if data['vocabulary']!=VOCABULARY:raise ValueError('Unknown lifecycle vocabulary')
    objects=data['objects']
    if not isinstance(objects,dict):raise ValueError('objects must be a dictionary')
    encoded={}
    for handle,obj in objects.items():
        keys(obj,{'category','name','properties'},{'category','name','properties'})
        if obj['category'] not in ENTITIES or not isinstance(obj['name'],str):raise ValueError('Unknown object category or name')
        p=obj['properties'];keys(p,set(ATTRIBUTES)|set(ENUMS)|{'transport_route'})
        event={'ev':ENTITIES[obj['category']],'id':obj['name']}
        for k,v in p.items():
            if k in ATTRIBUTES:event[ATTRIBUTES[k]]=copy.deepcopy(v)
            elif k in ENUMS:
                old,values=ENUMS[k]
                if v not in values:raise ValueError('Unknown lifecycle property value')
                event[old]=values[v]
            else:
                if not isinstance(v,list):raise ValueError('Route must be a list')
                event['path']=[]
                for step in v:
                    keys(step,{'relation','direction'},{'relation','direction'})
                    if step['direction'] not in ('forward','reverse'):raise ValueError('Invalid route direction')
                    event['path'].append([step['relation'],'ALONG' if step['direction']=='forward' else 'AGAINST'])
        encoded[handle]=event
    def history(steps):
        if not isinstance(steps,list):raise ValueError('History must be a list')
        out=[]
        for step in steps:
            keys(step,{'object','replacement'},{'object'})
            if step['object'] not in encoded:raise ValueError('History references an unknown object')
            e=copy.deepcopy(encoded[step['object']])
            if 'replacement' in step:
                replacement=step['replacement'];keys(replacement,{'prior','change'},{'prior','change'})
                if replacement['change'] not in CHANGES:raise ValueError('Unknown lifecycle change')
                e['supersedes']=replacement['prior'];e['discharge_kind']=CHANGES[replacement['change']]
            out.append(e)
        return out
    result={'records':history(data['history'])}
    if 'branch_comparison' in data:
        b=data['branch_comparison'];keys(b,{'common','first_branch','second_branch'},{'common','first_branch','second_branch'})
        result.update(prefix=history(b['common']),old=history(b['first_branch']),new=history(b['second_branch']))
    q=data['question'];keys(q,{'concerns','object','collection','successors'})
    if 'concerns' in q:
        if any(c not in CONCERNS for c in q['concerns']):raise ValueError('Unknown lifecycle concern')
        result['rules']=[CONCERNS[c] for c in q['concerns']]
    if 'object' in q:result['query_id']=q['object']
    if 'collection' in q:
        if q['collection']!='relations':raise ValueError('Unsupported collection question')
        result['registry']='edges'
    if 'successors' in q:result['successors']=copy.deepcopy(q['successors'])
    return result
