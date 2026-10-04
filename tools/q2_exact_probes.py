"""Bounded Q2 native arithmetic and reference countermodel probes.

Lean source is used as a hypothesis pointer only. No Lean compilation or
new kernel/checker admission is performed by these probes.
"""
from copy import deepcopy
from math import gcd

from grandportage import number_field as N
from grandportage import ordered as O
from grandportage import ordered_receipt as R
from grandportage import store as S


def _cubic(d):
    if (d['field'].get('base') != 'Q' or d['field'].get('symbol') != 'a'
            or d['model'].get('characteristic') != 0
            or d['model'].get('coefficient_domain') != 'Q'
            or d['model'].get('point_universe') != 'ALGEBRAIC_CLOSURE'
            or d['model'].get('ring_vars') != ['x']):
        raise ValueError('Unknown cubic witness context')
    control = d['control']
    if control in ('cubic_root', 'cubic_inverse', 'vanishing_guard'):
        if d['field']['minimal_polynomial'] != 'a^3-2':
            raise ValueError('Changed irreducible cubic')
    elif control == 'reducible_cubic':
        if d['field']['minimal_polynomial'] != 'a^3-a':
            raise ValueError('Changed reducible cubic')
    else:
        raise ValueError('Unknown cubic control')
    if control == 'cubic_root':
        if (d['model']['generators'] != ['x^3-2'] or d['model']['open_conditions'] != ['x']
                or d['coordinate'] != 'a'):
            raise ValueError('Changed cubic root case')
    elif control == 'cubic_inverse':
        if (d['model']['generators'] != ['2*x^3-1'] or d['model']['open_conditions'] != ['x']
                or d['coordinate'] != {'numerator':'1','denominator':'a'}):
            raise ValueError('Changed cubic inverse case')
    elif control == 'vanishing_guard':
        if (d['model']['generators'] != ['x^3-2']
                or d['model']['open_conditions'] != ['x^3-2'] or d['coordinate'] != 'a'):
            raise ValueError('Changed vanishing guard case')
    elif (d['model']['generators'] != ['x^3-2'] or d['model']['open_conditions'] != ['x']
          or d['coordinate'] != 'a'):
        raise ValueError('Changed reducible cubic case')
    try:
        ok, why, receipt = N.check_extension_witness(d['model'],
             {'kind': N.SCHEMA, **d['field']}, {'x': d['coordinate']})
    except N.NumberFieldError as exc:
        if control != 'reducible_cubic' or 'reducible' not in str(exc):
            raise
        return {'observed_verdict':'REFUSE','reason':str(exc),
                'native_result':'UNVERIFIABLE_FIELD','receipt':None,
                'external_execution':False}
    if control == 'reducible_cubic':
        raise ValueError('Reducible cubic unexpectedly admitted')
    if control == 'vanishing_guard':
        if ok or 'guard' not in why:
            raise ValueError('Vanishing guard unexpectedly passed')
        return {'observed_verdict':'REFUSE','reason':why,
                'native_is_point':ok,'receipt':receipt,'external_execution':False}
    if not ok or receipt is None:
        raise ValueError('Positive cubic witness did not verify')
    return {'observed_verdict':'ACCEPT','reason':why,'native_is_point':ok,
            'receipt':receipt,'external_execution':False}


def _ordered(d):
    if (d['field']!='Q' or d['point_universe']!='REAL_CLOSURE'
            or d['interval'] not in (['1','2'],['2','3'])):
        raise ValueError('Unknown ordered root context')
    expected={
        'repeated_interior':('(w^2-2)^2',['1','2'],'w',1),
        'common_factor_zero':('(w^2-2)^2',['1','2'],'w^2-2',0),
        'repeated_endpoint':('(w-2)^2',['2','3'],'w',1),
        'tampered_sign':('(w^2-2)^2',['1','2'],'w',-1),
    }
    if d['control'] not in expected or (d['generator'],d['interval'],d['expression'],d['claimed_sign'])!=expected[d['control']]:
        raise ValueError('Changed ordered sign fixture')
    model={'ev':'model','id':'M','what':'M','coefficient_domain':'Q',
           'characteristic':0,'point_universe':S.REAL_CLOSURE_POINT_UNIVERSE,
           'ring_vars':['w'],'generators':[d['generator']],
           'embedding':{'var':'w','kind':'REAL',
                        'isolating_interval':{'lo':d['interval'][0],'hi':d['interval'][1]}}}
    sign,receipt=O.selected_real_sign(model,d['expression'])
    replayed=R.verify(model,d['expression'],receipt)
    if replayed!=sign:
        raise ValueError('Producer and exact receipt replay disagree')
    if d['control']=='tampered_sign':
        if sign!=1:
            raise ValueError('Positive receipt control changed')
        tampered=deepcopy(receipt);tampered['sign']=d['claimed_sign']
        try:R.verify(model,d['expression'],tampered)
        except R.OrderedReceiptError as exc:
            return {'observed_verdict':'REFUSE','reason':str(exc),
                    'correct_sign':sign,'tampered_sign':d['claimed_sign'],
                    'positive_receipt_replayed':True,'external_execution':False}
        raise ValueError('False sign receipt unexpectedly replayed')
    if sign!=d['claimed_sign']:
        raise ValueError('Exact sign differs from positive claim')
    return {'observed_verdict':'ACCEPT','reason':'Exact selected-root sign and independent receipt replay agree.',
            'exact_sign':sign,'receipt':receipt,'external_execution':False}


def _zero_algebra(d):
    if d!={'control':'zero_algebra_unit','carrier_size':1,'zero':0,'one':0,
           'equations':['x','1-x'],'cofactors':['1','1'],'point':{'x':0},
           'deleted_premise':'one_ne_zero'}:
        raise ValueError('Unknown zero-algebra countermodel')
    zero=one=x=0
    equation_values=[x,(one-x)%1]
    cofactor_sum=sum(equation_values)%1
    if equation_values!=[0,0] or cofactor_sum!=one or one!=zero:
        raise ValueError('Zero-algebra countermodel arithmetic failed')
    # In Z, x=0 and 1-x=0 are incompatible: substituting x=0 gives 1=0.
    integer_positive_control={'x_for_first_equation':0,
                              'second_equation_at_x_zero':1,
                              'simultaneous_integer_point':False}
    return {'observed_verdict':'REFUSE',
            'reason':'In the one-element algebra, 1=0 and both generators vanish at its point, so the unit derivation alone does not exclude a point.',
            'reference_equation_values':equation_values,'one_equals_zero':True,
            'reference_point_exists':True,'integer_nontrivial_positive_control':integer_positive_control,
            'native_lean_verdict':None,'external_execution':False}


def _fin4(d):
    if d!={'control':'fin4_cancellation','modulus':4,'c':2,'g':2,
           'equation':'c*g=0','coefficient_nonzero':True,
           'deleted_premise':'no_zero_divisors'}:
        raise ValueError('Unknown Fin4 cancellation countermodel')
    c=g=2;product=(c*g)%4
    no_zero_divisors_fin2=all((a*b)%2!=0 or a==0 or b==0
                              for a in range(2) for b in range(2))
    if product!=0 or c%4==0 or g%4==0 or not no_zero_divisors_fin2:
        raise ValueError('Finite algebra control failed')
    return {'observed_verdict':'REFUSE',
            'reason':'In Fin4, c=g=2 are nonzero and c*g=0; cancellation needs no-zero-divisors.',
            'reference_product_mod_four':product,'factors_nonzero':True,
            'fin2_no_zero_divisors_positive_control':no_zero_divisors_fin2,
            'native_lean_verdict':None,'external_execution':False}


def _sixes(d):
    if d!={'control':'sixes_saturation','ambient':'Z',
           'source_ideal_generator':6,'recorded_output_generator':6,
           'recorded_generators':[6],'saturating_element':2,
           'missing_element':3,'source_containment_checked':True,
           'no_invented_generator_checked':True}:
        raise ValueError('Unknown stronger-premise saturation countermodel')
    # I=J=(6) establishes source containment, and generator 6 has witness 1.
    contains_source=True
    generator_saturation_witness=(1*6)%6==0
    missing_saturation_witness=(2*3)%6==0
    missing_in_output=3%6==0
    if (not contains_source or not generator_saturation_witness
            or not missing_saturation_witness or missing_in_output
            or gcd(2,3)!=1):
        raise ValueError('Stronger-premise saturation arithmetic failed')
    return {'observed_verdict':'REFUSE',
            'reason':'I=J=(6) passes source containment and generator no-invention, but 2*3=6 puts 3 in the saturation while 3 is not in J.',
            'contains_source':contains_source,
            'no_invented_generator':generator_saturation_witness,
            'missing_element_saturation_witness_multiplier':2,
            'missing_element_in_recorded_output':missing_in_output,
            'exact_saturation_generator':3,
            'exact_saturation_argument':'2*g divisible by 6 iff g divisible by 3; gcd(2,3)=1',
            'native_lean_verdict':None,'external_execution':False}


def probe(case, route):
    d=case['inputs']
    if route['layer']=='native_exact_cubic':return _cubic(d)
    if route['layer']=='native_exact_selected_sign':return _ordered(d)
    if route['layer']=='reference_zero_algebra':return _zero_algebra(d)
    if route['layer']=='reference_fin4_cancellation':return _fin4(d)
    if route['layer']=='reference_sixes_saturation':return _sixes(d)
    raise ValueError('Unknown Q2 exact probe layer')
