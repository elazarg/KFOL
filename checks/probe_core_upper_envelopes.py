"""Test unrestricted word-upper meets at fixed valuations, for ALL term sizes.

This probes an open conjecture, not finite basability. It uses the native
three-owner core as the reference algebra, and certified core models as
targets. By default it checks every four-variable valuation, up to variable
permutation, in the stored three-owner models.

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
to checking it for every term at this valuation. Indeed, upper bounds for
P[a] are upper bounds for every term with value a, and P[a] itself is a term
with value a. No term-size or translation-depth cutoff is used. The number
of variables and the target algebras are still bounded in each run.
"""

import argparse
import random
from collections import deque
from functools import lru_cache
from itertools import combinations_with_replacement

from check_core_owned_reset import test_models


@lru_cache(maxsize=None)
def variable_profiles(arity):
    """Three bitsets per function, over all 7**arity native assignments.

    Native values are the nonempty subsets 1,...,7 of three owners. Bit r
    in component i records whether owner i belongs to the output at row r.
    """
    mask = (1 << (7 ** arity)) - 1
    profiles = []
    for i in range(arity):
        width = 7 ** (arity - i - 1)
        repetitions = mask // ((1 << (7 * width)) - 1)
        block = repetitions * ((1 << width) - 1)
        profiles.append(tuple(
            sum(block << (a * width) for a in range(7) if (a + 1) >> k & 1)
            for k in range(3)))
    return profiles


def native_operation(owner, left, right):
    """Operation 0 is join; operations 1,...,3 are the owned choices."""
    result = [a | b for a, b in zip(left, right)]
    if owner:
        i = owner - 1
        j, k = (i + 1) % 3, (i + 2) % 3
        absorbing = ((left[i] & ~(left[j] | left[k]))
                     | (right[i] & ~(right[j] | right[k])))
        result[j] &= ~absorbing
        result[k] &= ~absorbing
    return tuple(result)


def native_below(left, right):
    return all(a | b == b for a, b in zip(left, right))


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
    parser.add_argument('--seed', type=int, default=62610)
    args = parser.parse_args()
    if args.variables < 1 or args.samples < 0:
        parser.error('variables must be positive and samples nonnegative')
    rng = random.Random(args.seed)
    checked = models_checked = 0
    # The last four test models are D_K, which fail owner exhaustion.
    for index, (join, choices) in enumerate(test_models()[:-4]):
        if len(choices) != 3 or (args.model is not None and index != args.model):
            continue
        models_checked += 1
        operations = [join] + choices
        valuations = (combinations_with_replacement(range(len(join)), args.variables)
                      if not args.samples else
                      ([rng.randrange(len(join)) for _ in range(args.variables)]
                       for _ in range(args.samples)))
        for valuation in valuations:
            failure = check_valuation(operations, valuation)
            checked += 1
            if failure is not None:
                raise AssertionError((index, tuple(valuation), failure))
    if not models_checked:
        parser.error('no certified three-owner model selected')
    print(f'Unrestricted upper meets: all term sizes passed at {checked} '
          f'{args.variables}-variable valuations in {models_checked} models '
          f'({"sampled" if args.samples else "exhaustive up to variable permutation"}). '
          'This does not settle arbitrary arity or finite basability.')


if __name__ == '__main__':
    main()
