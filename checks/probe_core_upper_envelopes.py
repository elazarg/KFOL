"""Test unrestricted word-upper meets at fixed valuations, for ALL term sizes.

This tests a property that fails in general; the five-variable obstruction
is certified by check_core_upper_meet_obstruction.py. It does not decide
finite basability. It uses the three
four-element observers of the native three-owner core as reference algebras,
and certified core models as targets. By default it checks every
four-variable valuation, up to variable permutation, in the stored models.

For a fixed target valuation, keep the pointwise join P[a] of the native
functions of terms whose target value is a. Starting with the variables,
close these profiles under all basic operations and join profiles with the
same target value. Every profile is attained: joining terms with value a
still has value a. Native monotonicity proves by induction that the final
P[a] majorizes every term with target value a. Thus P[a] is their maximum.

For words, use only translations by original variables. Joining profiles
with the same target value remains sound because translations distribute
over join: the profile is attained by a join of variable-coefficient words.
Joining these profiles over states <= m gives exactly the largest native
function of a word-join term with target value <= m. Therefore P[a] lies
below this envelope iff some such term is a universal upper bound for it.

Checking the greatest-lower-bound assertion for every P[a] is equivalent
to checking it for every term at this valuation IN A CORE ALGEBRA. Indeed,
upper bounds for P[a] are upper bounds for every term with value a, and
every native-valid upper bound of such a term remains above a in the
target. Conversely, P[a] itself is a term with value a. This use of known
core membership is essential: passing is not a membership certificate for
an arbitrary candidate algebra. No term-size or word-depth cutoff is used.
The fixed-valuation calculation alone still bounds the number of variables.

There is also an all-arity reduction for a FIXED finite target algebra.
Group variables with equal target values, replacing each group by its join.
Monotonicity puts the original term below the resulting term in distinct
group variables, with the same target value. Any word-join upper bound for
the grouped term expands, by distribution, to a word-join upper bound in
the original variables, preserving its target value. Consequently checking
every nonempty subset of target elements as distinct variable values covers
all arities. Use --all-subsets --max-size 8 for the stored small models.
"""

import argparse
import random
from collections import deque
from functools import lru_cache
from itertools import chain, combinations, combinations_with_replacement

from check_core_owned_reset import test_models


@lru_cache(maxsize=None)
def variable_profiles(arity):
    """Three bitsets per observer, over all 4**arity assignments in each.

    In the observer omitting owner j, the two remaining owners in increasing
    order label atoms alpha,beta; n,p are the markers. Each block records
    the rows with output alpha, beta, or p (n is the complement). Core
    inequalities hold iff they hold in all three observers. The observer
    homomorphism sends a singleton of a retained owner to its atom, the pair
    of retained owners to n, and every set containing j to p. Together the
    three maps embed the native seven-element core.
    """
    mask = (1 << (4 ** arity)) - 1
    profiles = []
    for i in range(arity):
        width = 4 ** (arity - i - 1)
        repetitions = mask // ((1 << (4 * width)) - 1)
        block = repetitions * ((1 << width) - 1)
        profiles.append((block, block << width, block << (3 * width)) * 3)
    return profiles


def native_operation(owner, left, right):
    """Operation 0 is join; operations 1,...,3 are the owned choices."""
    result = []
    for omitted in range(3):
        offset = 3 * omitted
        a, b, p = left[offset:offset + 3]
        c, d, q = right[offset:offset + 3]
        retained = [i for i in range(3) if i != omitted]
        if owner == 0 or owner - 1 == omitted:
            result.extend((a & c, b & d, p | q))
        elif owner - 1 == retained[0]:
            result.extend((a | c, b & d, (p | q) & ~(a | c)))
        else:
            result.extend((a & c, b | d, (p | q) & ~(b | d)))
    return tuple(result)


def native_below(left, right):
    return all(not (right[i] & ~left[i] or right[i + 1] & ~left[i + 1]
                    or left[i + 2] & ~right[i + 2]) for i in (0, 3, 6))


def maximal_profiles(operations, valuation, *, words):
    variables = variable_profiles(len(valuation))
    profiles = [None] * len(operations[0])
    pending = deque()
    queued = set()

    def add(state, profile):
        old = profiles[state]
        new = profile if old is None else native_operation(0, old, profile)
        if new != old:
            profiles[state] = new
            if state not in queued:
                pending.append(state)
                queued.add(state)

    for state, profile in zip(valuation, variables):
        add(state, profile)
    while pending:
        state = pending.popleft()
        queued.remove(state)
        profile = profiles[state]
        coefficients = (list(zip(valuation, variables)) if words else
                        [(s, p) for s, p in enumerate(profiles) if p is not None])
        for other, other_profile in coefficients:
            for h, operation in enumerate(operations):
                add(operation[state][other],
                    native_operation(h, profile, other_profile))
    return profiles


def check_valuation(operations, valuation):
    """Return a failed meet (target, extra lower bound, upper thresholds)."""
    add = operations[0]
    size = len(add)
    words = maximal_profiles(operations, valuation, words=True)
    terms = maximal_profiles(operations, valuation, words=False)
    envelopes = []
    for bound in range(size):
        envelope = None
        for state, profile in enumerate(words):
            if profile is not None and add[state][bound] == bound:
                envelope = (profile if envelope is None else
                            native_operation(0, envelope, profile))
        envelopes.append(envelope)
    for state, profile in enumerate(terms):
        if profile is None:
            continue
        uppers = [bound for bound, envelope in enumerate(envelopes)
                  if envelope is not None and native_below(profile, envelope)]
        # The input models belong to the core variety, so validity puts
        # every upper threshold above the target. Check this independently.
        assert uppers and all(add[state][bound] == bound for bound in uppers)
        for lower in range(size):
            if (add[lower][state] != state
                    and all(add[lower][bound] == bound for bound in uppers)):
                return state, lower, uppers
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variables', type=int, default=4)
    parser.add_argument('--samples', type=int, default=0,
                        help='random valuations per model; zero enumerates all')
    parser.add_argument('--model', type=int,
                        help='index in check_core_owned_reset.test_models()')
    parser.add_argument('--max-size', type=int, help='maximum target algebra size')
    parser.add_argument('--all-subsets', action='store_true',
                        help='all arities via nonempty subsets of target elements')
    parser.add_argument('--seed', type=int, default=62610)
    args = parser.parse_args()
    if args.variables < 1 or args.samples < 0:
        parser.error('variables must be positive and samples nonnegative')
    if args.all_subsets and args.samples:
        parser.error('--all-subsets requires exhaustive enumeration')
    if args.all_subsets and args.max_size is None and args.model is None:
        parser.error('--all-subsets requires --max-size or --model')
    rng = random.Random(args.seed)
    checked = models_checked = 0
    # The last four test models are D_K, which fail owner exhaustion.
    for index, (join, choices) in enumerate(test_models()[:-4]):
        if len(choices) != 3 or (args.model is not None and index != args.model):
            continue
        if args.max_size is not None and len(join) > args.max_size:
            continue
        models_checked += 1
        operations = [join] + choices
        if args.all_subsets:
            valuations = chain.from_iterable(combinations(range(len(join)), d)
                                             for d in range(1, len(join) + 1))
        elif args.samples:
            valuations = ([rng.randrange(len(join)) for _ in range(args.variables)]
                          for _ in range(args.samples))
        else:
            valuations = combinations_with_replacement(range(len(join)), args.variables)
        for valuation in valuations:
            failure = check_valuation(operations, valuation)
            checked += 1
            if failure is not None:
                raise AssertionError((index, tuple(valuation), failure))
    if not models_checked:
        parser.error('no certified three-owner model selected')
    scope = 'all-arity subset' if args.all_subsets else f'{args.variables}-variable'
    print(f'Unrestricted upper meets: all term sizes passed at {checked} '
          f'{scope} valuations in {models_checked} models '
          f'({"sampled" if args.samples else "exhaustive up to variable permutation"}). '
          'This does not settle arbitrary target algebras or finite basability.')


if __name__ == '__main__':
    main()
