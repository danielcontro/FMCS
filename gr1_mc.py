# Imports

import sys
import pynusmv
from enum import Enum
from collections import deque
from pynusmv_lower_interface.nusmv.parser import parser

# Types

from typing import Optional, Set, Tuple, List, Dict
from pynusmv.dd import BDD, Inputs, State
from pynusmv.fsm import BddFsm
from pynusmv.prop import Spec

# Types aliases and utility classes

Start = BDD
End = BDD
Filter = BDD
PostReach = BDD
PreReach = BDD
Reach =  PreReach | PostReach
Recur = BDD
Frontiers = List[BDD]
Path = List[State]
Loop = List[State]
Counterexample = Tuple

class Method(Enum): PRE = 1; POST = 2

# Constants

DEBUG = True

SPEC_TYPES = {
    'LTLSPEC': parser.TOK_LTLSPEC,
    'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES,
    'IFF': parser.IFF,
    'OR': parser.OR,
    'XOR': parser.XOR,
    'XNOR': parser.XNOR,
    'AND': parser.AND,
    'NOT': parser.NOT,
    'ATOM': parser.ATOM,
    'NUMBER': parser.NUMBER,
    'DOT': parser.DOT,
    'NEXT': parser.OP_NEXT,
    'OP_GLOBAL': parser.OP_GLOBAL,
    'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL,
    'NOTEQUAL': parser.NOTEQUAL,
    'LT': parser.LT,
    'GT': parser.GT,
    'LE': parser.LE,
    'GE': parser.GE,
    'TRUE': parser.TRUEEXP,
    'FALSE': parser.FALSEEXP
}

BASIC_TYPES = {
    parser.ATOM,
    parser.NUMBER,
    parser.TRUEEXP,
    parser.FALSEEXP,
    parser.DOT,
    parser.EQUAL,
    parser.NOTEQUAL,
    parser.LT,
    parser.GT,
    parser.LE,
    parser.GE
}

BOOLEAN_OP = {
    parser.AND,
    parser.OR,
    parser.XOR,
    parser.XNOR,
    parser.IMPLIES,
    parser.IFF
}

def spec_to_bdd(model: BddFsm, spec: Spec) -> BDD:
    """
    Given a formula `spec` with no temporal operators, returns a BDD
    equivalent to the formula, that is, a BDD that contains all the states of
    `model` that satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec
    
def is_boolean_formula(spec) -> bool:
    """
    Given a formula `spec`, checks if the formula is a boolean combination of
    base formulas with no temporal operators.
    """
    if spec.type in BASIC_TYPES:
        return True
    elif spec.type == SPEC_TYPES['NOT']:
        return is_boolean_formula(spec.car)
    elif spec.type in BOOLEAN_OP:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False

def is_GF_formula(spec) -> bool:
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f
    is a boolean combination of base formulas with no temporal operators
    """
    # check if formula is of type GF f_i
    if spec.type != SPEC_TYPES['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != SPEC_TYPES['OP_FUTURE']:
        return False
    return is_boolean_formula(spec.car)

def create_set_of_formulas(spec) -> Optional[Set[Spec]]:
    """
    Given a formula `spec` of the form

                    (GF f_1 & ... & GF f_n) 

    where f_1, ..., f_n are boolean combination of basic formulas, returns the
    set of formulas {f_1, ..., f_n}.
    If `spec` is not in the required form, then the result is None.
    """
    f_set = set()
    working = deque()
    working.append(spec)
    while working:
        # next formula to analyse
        head = working.pop()
        if head.type == SPEC_TYPES['AND']:
            # push conjuncts into the queue
            working.append(head.car)
            working.append(head.cdr)
        else:
            # check if it is a GF-formula
            if not is_GF_formula(head):
                return None
            # add boolean formula to the set
            f_set.add(head.car.car)
    return f_set

def parse_gr1(spec) -> Optional[Tuple[Set[Spec], Set[Spec]]]:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a
    GR(1) formula, that is wether the formula is of the form

                    (GF f_1 & ... & GF f_n) -> (GF g_1 & ... & GF g_m)

    where f_1, ..., f_n, g_1, ..., g_m are boolean combination of basic
    formulas.

    If `spec` is a GR(1) formula, the result is a pair where the first
    element is the set of formulas {f_1, ..., f_n} and the second element
    is the set {g_1, ..., g_m}.
    If `spec` is not a GR(1) formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != SPEC_TYPES['CONTEXT']:
        return None
    else:
        # the right child of a context is the main formula
        spec = spec.cdr
        # the root of a GR(1) formula should be of type IMPLIES
        if spec.type != SPEC_TYPES['IMPLIES']:
            return None
        # Create the set of formulas for the lhs of the implication
        f_set = create_set_of_formulas(spec.car)
        if f_set == None:
            return None
        # Create the set of formulas for the rhs of the implication
        g_set = create_set_of_formulas(spec.cdr)
        if g_set == None:
            return None
        return (f_set, g_set)

_REACHES: Dict[Tuple[Method, Start, Filter], Tuple[Reach, Frontiers]] = {}

def reachable_states_from_region(ts: BddFsm, start: Start, method: Method, filter : Filter) -> Tuple[Reach, Frontiers]:
    '''
    Computes the reachable states of the `ts` transition system starting from
    the `start` region using the `method` given and filtering them using the
    `filter` region.

    Returns a tuple with the reachable states and the frontiers explored
    during the computation.
    '''
    result = _REACHES.get((method, start, filter))
    if result != None: return result

    if method == Method.PRE: reach_method = ts.pre
    elif method == Method.POST: reach_method = ts.post

    reach = start & filter
    frontiers = [reach]
    while frontiers[-1].isnot_false():
        frontiers.append((reach_method(frontiers[-1]) - reach) & filter)
        reach = reach | frontiers[-1]
    _REACHES[(method, start, filter)] = (reach, frontiers)
    return reach, frontiers

def phi_repeatable_from_region(ts: BddFsm, phi: Spec, start: Start, filter : Filter) -> Tuple[Recur, PreReach]:
    '''
    Computes the states of the `ts` transition system where the base formula
    `phi` is repeatable starting from the `start` region and filtering them
    with the `filter` region.

    Returns the region of states where the base formula `phi`
    is repeatable and the region of states from which the repeatable region
    can be reached.
    '''
    recur = start & spec_to_bdd(ts, phi) & filter
    while recur.isnot_false():
        pre_reach = BDD.false()
        new = ts.pre(recur) & filter
        while new.isnot_false():
            pre_reach = pre_reach | new
            if recur.entailed(pre_reach): return recur, pre_reach
            new = (ts.pre(new) - pre_reach) & filter
        recur = recur & pre_reach
    return BDD.false(), BDD.false()

def region_fixpoint(ts: BddFsm, method: Method, start: Start) -> BDD:
    """
    Computes a fixpoint of the `start` region using the `method` given.

    Returns a fixpoint of the `start` region.
    """
    if method == Method.POST: fixpoint_method = ts.post
    elif method == Method.PRE: fixpoint_method = ts.pre
    current = start
    while current.isnot_false():
        next = fixpoint_method(current) & current
        if current.equal(next): return current
        current = next
    return BDD.false()

def f_set_repeatable(ts: BddFsm, f_set: Set[Spec], reach: PostReach) ->  Tuple[List[Recur], Filter]:
    """
    Computes the list of recur regions of the `ts` transition system for the
    given set of base formulas `f_set` starting from the `reach` region

    Returns the list of recur regions and the region within which there exists
    loops passing through each recur region.
    """
    fi_recur = BDD.false()
    fi_recurs = []
    loopable_region = reach

    for fi in iter(f_set):
        fi_recur, pre_reach = phi_repeatable_from_region(ts, fi, loopable_region, loopable_region)
        if fi_recur.is_false(): return [], BDD.false()
        # There exist a set of states satisfying fᵢ ∧ ◻◇fᵢ
        fi_recurs.append(fi_recur)
        loopable_region, _ = reachable_states_from_region(ts, fi_recur, Method.POST, pre_reach)
    return fi_recurs, loopable_region

def repeat_check(ts: BddFsm, phi: Spec, reach: PostReach):
    repeatable_region, _ = phi_repeatable_from_region(ts, phi.car.car, reach, BDD.true())
    repeatable = repeatable_region.isnot_false() 
    check_neg_persistent, counterexample = pynusmv.mc.check_explain_ltl_spec(pynusmv.prop.not_(phi))
    check_repeatable = not check_neg_persistent
    if DEBUG:
        print("Spec:", phi)
        if check_repeatable == repeatable: print("Repeatability correct:", repeatable)
        else:
            print("Repeatability wrong: expected", check_repeatable,"got", repeatable) 
            if check_repeatable == False: print("Counterexample:", counterexample)

def get_index_of(region: BDD, frontiers: Frontiers) -> Optional[int]:
    """
    Returns the index of the first frontier of `frontiers` that intersects
    `region` or None if none does intersects it.
    """
    for idx, frontier in enumerate(frontiers):
        if frontier.intersected(region): return idx
    return None

def get_path(ts: BddFsm, start: Start, end: End, filter: Filter, ensure_transition: bool = False) -> Optional[Path]:
    """
    Returns a path starting from `start` to `end` withing the `filter` region,
    ensuring at least one transition if the flag `ensure_transition` is set to
    `True` or None if such path doesn't exists.
    """
    add_ts = False
    first = start & filter
    end = end & filter
    if first.intersected(end):
        # If end appears in the first frontier then keep the intersection
        end = first & end
        if ensure_transition:
            add_ts = True
            first = ts.post(first) & filter

    current_region = end & filter
    path = [ ts.pick_one_state(current_region) ]
    first_reach, frontiers = reachable_states_from_region(ts, first, Method.POST, filter)
    if not first_reach.intersected(end): return None

    match get_index_of(end, frontiers):
        case None: return None
        case index: end_index = index

    for i in range(end_index-1, -1, -1):
        current_region = frontiers[i] & ts.pre(path[-1])
        path.append(ts.pick_one_state(current_region))

    if add_ts:
        current_region = start & ts.pre(first)
        path.append(ts.pick_one_state(current_region))

    # Since the path is built from the end to start it must be reversed to be in the correct order
    return path[::-1]

def recursive_get_loop_through_regions(ts: BddFsm, regions: List[BDD], reach_frontiers: Frontiers, filter: Filter) -> Optional[Loop]:
    start_region = regions[-1] & filter
    # check if there exist a loop of length >= 1
    if start_region.is_false(): return None
    # restricts the starting region to the intersection between fn_recur and f₀_recur if it isn't empty
    if start_region.intersected(regions[0]): start_region = start_region & regions[0]
    # restricts the starting region to the intersection between itself and the initial states if it isn't empty
    if start_region.intersected(ts.init): start_region = start_region & ts.init
    loop = None
    while loop == None:
        start_index = get_index_of(start_region, reach_frontiers)
        if start_index == None: return None
        # Look for the closest loop
        start = ts.pick_one_state(start_region & reach_frontiers[start_index])
        start_region = start_region - start
        loop = aux_recursive_get_loop_through_regions(ts, start, start, regions[:-1], filter)
    return loop

def aux_recursive_get_loop_through_regions(ts: BddFsm, start: State, prev: State, regions: List[BDD], filter: Filter) -> Optional[Path]:
    match regions:
        case []: return get_path(ts, prev, start, filter, True)
        case [f_rec, *regions]:
            segment = None
            loop_segment = None
            current_region = f_rec & filter
            while loop_segment == None:
                _, frontiers = reachable_states_from_region(ts, prev, Method.POST, filter)
                index = get_index_of(current_region, frontiers)
                # No intersection between the frontiers of the previous state and the current region, thus the previous state must be changed
                if index == None: return None
                next_state = ts.pick_one_state(current_region & frontiers[index])
                segment = get_path(ts, prev, next_state, filter)
                if segment != None: loop_segment = aux_recursive_get_loop_through_regions(ts, start, next_state, regions, filter)
                current_region = current_region - next_state
            if segment == None: return None
            return segment + loop_segment[1:]

def get_loop_through_regions(ts: BddFsm, regions: List[BDD], reach_frontiers: Frontiers, filter: Filter) -> Optional[Loop]:
    """
    Returns a loop of the `ts` transition system within the `filter` region
    that traverses each region of `regions` or None if such a loop
    doesn't exists.
    """
    start_region = regions[-1] & filter
    # check if there exist a loop of length >= 1
    if start_region.is_false(): return None
    # restricts the starting region to the intersection between fn_recur and f₀_recur if it isn't empty
    if start_region.intersected(regions[0]): start_region = start_region & regions[0]
    # restricts the starting region to the intersection between itself and the initial states if it isn't empty
    if start_region.intersected(ts.init): start_region = start_region & ts.init

    waypoint_regions = regions

    while True:
        start_index = get_index_of(start_region, reach_frontiers)
        if start_index == None: return None
        # Look for the closest loop
        start = ts.pick_one_state(start_region & reach_frontiers[start_index])
        start_region = start_region - start
        # If start isn't in its post region pick another one
        if not reachable_states_from_region(ts, ts.post(start), Method.POST, filter)[0].intersected(start): continue
        loop = loop_waypoints = [start]
        loop_region = start

        while i := len(loop_waypoints):
            _, frontiers = reachable_states_from_region(ts, loop_waypoints[-1], Method.POST, filter)
            # Chech if the loop has to be closed or not
            if i == len(regions): current_region = start
            else: current_region = waypoint_regions[i-1] & filter

            index = get_index_of(current_region, frontiers)
            start_index = get_index_of(start, frontiers)
            # If there's no path between the previous loop waypoint and the current region or to the starting state
            if index == None or start_index == None:
                # The previous loop waypoint must be removed and the current f_rec reinitialised as the original one
                waypoint_regions[i-1] = regions[i-1]
                loop_waypoints.pop()
                # And then try looking for a path with a different state 
                continue
            # Greedily pick the closest state reachable from the previous loop waypoint not yet removed from f_rec[i-1]
            next_state = ts.pick_one_state(current_region & frontiers[index])
            waypoint_regions[i-1] = waypoint_regions[i-1] - next_state

            segment = get_path(ts, loop_waypoints[-1], next_state, filter, i==len(regions))
            if segment == None: break

            loop = loop + segment[1:]
            if i == len(regions): return loop
            for state in segment: loop_region = loop_region + state
            loop_waypoints.append(next_state)

def get_index_of_init_intersection(ts: BddFsm, path: Path) -> Optional[int]:
    """
    Returns the index of the first state in path that intersects the
    initial states of the `ts` transition system or None if `path` doesn't
    intersect it.
    """
    for i, state in enumerate(path):
        if state.intersected(ts.init): return i
    return None

def rotate_loop(ts: BddFsm, loop: Loop) -> Loop:
    """
    Returns the given `loop` rotated in case a different state from the first
    one intersects the initial states or itself otherwise.
    """
    index = get_index_of_init_intersection(ts, loop)
    if index == None or index == 0: return loop
    if DEBUG: print("Rotated by", index)
    return loop[index:-1] + loop[:index] + [loop[index]]

def get_counterexample(ts: BddFsm, recurs: List[Recur], loop_region: BDD, reach_frontiers: Frontiers) -> Optional[Tuple[Counterexample, Path, List[Inputs]]]:
    """
    Returns an execution of the `ts` transition system that has a loop that
    passes through each recur region of `recurs` and which stays within the
    `loop_region`.
    """
    loop = get_loop_through_regions(ts, recurs, reach_frontiers, loop_region)
    if loop == None: return None
    loop = rotate_loop(ts, loop)
    if DEBUG:
        print("Loop region size:", ts.count_states(loop_region))
        print("Loop start in init", ts.init.intersected(loop[0]))
        print("Loop:")
        print([state.get_str_values() for state in loop])
    prefix = get_path(ts, ts.init, loop[0], BDD.true())
    if prefix == None: return None
    if DEBUG:
        print("Prefix")
        print([state.get_str_values() for state in prefix])
        if not prefix[-1].equal(loop[0]) or not prefix[-1].equal(loop[-1]): print("Loop not aligned")
        print("Loop starts at state", len(prefix))
    states = prefix[:-1] + loop
    inputs : List[Inputs] = []
    counterexample : List[Dict] = []

    has_inputs = len(ts.bddEnc.inputsVars) > 0

    for i in range(len(states) - 1):
        if not ts.post(states[i]).intersected(states[i+1]): raise Exception("No transition between states", i, "and", i+1)
        counterexample.append(states[i].get_str_values())
        if has_inputs:
            inputs.append(ts.pick_one_inputs(ts.get_inputs_between_states(states[i], states[i+1])))
            counterexample.append(inputs[-1].get_str_values())
        else:
            counterexample.append({})
    counterexample.append(states[-1].get_str_values())
    return tuple(counterexample), states, inputs

def check_explain_gr1_spec(spec: Spec) -> Optional[Tuple[bool, Optional[Counterexample]]]:
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise. 

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. The execution is looping if the last state is somewhere 
    else in the sequence. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    parse_result = parse_gr1(spec)
    if parse_result == None: return None

    ts = pynusmv.glob.prop_database().master.bddFsm
    f_set, g_set = parse_result
    reach, reach_frontiers = reachable_states_from_region(ts, ts.init, Method.POST, BDD.true())

    if DEBUG:
        if reach.equal(ts.reachable_states | ts.init): print("Reachability: correct")
        else: print("Reachability: wrong")

    """
    For each `g` in `g_set` look for a counterexample of the desired propery
    """
    for gi in iter(g_set):
        # Reachable states satisfying ¬gᵢ
        neg_gi_reach = reach & (- spec_to_bdd(ts, gi))
        # Reachable states satisfying ¬g where there exist a loop that satisfies □¬g
        neg_gi_loopable_region = region_fixpoint(ts, Method.POST, neg_gi_reach)
        """
        There isn't a reachable loop satisfying ◻¬gᵢ, hence there can't be a counterexample with
        the current gᵢ, thus proceed with gᵢ₊₁
        """
        if neg_gi_loopable_region.is_false(): continue

        """
        Compute the f_recur region, which is the region where there exist a path of at least one
        transition that satisfies fᵢ ∀ i ∈ n
        """
        f_set_recurs, f_set_recur_loopable_region = f_set_repeatable(ts, f_set, neg_gi_loopable_region)
        if len(f_set_recurs) > 0:
            if DEBUG: print("G not respected:", gi)
            if (result := get_counterexample(ts, f_set_recurs, f_set_recur_loopable_region, reach_frontiers)) == None: raise Exception("Counterexample not found")
            counterexample, states, _ = result
            if DEBUG:
                check_verified, check_counter_example = pynusmv.mc.check_explain_ltl_spec(spec)
                if check_verified:
                    print("GR1 satisfiability: wrong")
                    print("Expected True, got False: T -> F")
                else:
                    print("GR1 satisfiability: correct")
                    print("PyNuSMV counterexample:", check_counter_example)
                if not ts.init.intersected(states[0]): print("First state of counterexample not in initial states")
            return False, counterexample
    if DEBUG:
        check_verified, check_counter_example = pynusmv.mc.check_explain_ltl_spec(spec)
        if check_verified: print("GR1 satisfiability correct")
        else:
            print("GR1 satisfiability: wrong")
            print("Expected False, got True")
            print(check_counter_example)
    return True, None

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        print("")
        print("Spec:", spec)
        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        if (result := check_explain_gr1_spec(spec)) == None:
            print('Property is not a GR(1) formula, skipping')
        elif result[0] == True:
            print("Property is respected")
        elif result[0] == False and result[1] != None:
            print("Property is not respected")
            print("Counterexample:", result[1])
        print()

    pynusmv.init.deinit_nusmv()
