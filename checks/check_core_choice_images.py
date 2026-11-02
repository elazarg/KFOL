"""Verify a universal equational derivation of choice-image closure.

The certificate was found by Prover9 and expanded by prooftrans. This
checker does not invoke either program: it independently checks each
substitution and replacement. The assumptions are the two-owner part of
Gamma plus mixed absorption, the two bound equations already derived
from Gamma in the paper, and f(c,a)=a, f(c,b)=b. The conclusion is
f(c,g(a,b))=g(a,b), over arbitrary algebras, not just finite tables.
"""

import json
import re
from collections import Counter
from itertools import product
from pathlib import Path


VARIABLE = re.compile(r'[u-z][A-Za-z0-9_]*\Z')
ASSUMPTIONS = (
    'f(x,x)=x', 'f(x,y)=f(y,x)', 'f(x,f(y,z))=f(f(x,y),z)',
    'g(x,x)=x', 'g(x,y)=g(y,x)', 'g(x,g(y,z))=g(g(x,y),z)',
    'j(x,x)=x', 'j(x,y)=j(y,x)', 'j(x,j(y,z))=j(j(x,y),z)',
    'f(x,j(y,z))=j(f(x,y),f(x,z))',
    'g(x,j(y,z))=j(g(x,y),g(x,z))',
    'j(f(x,y),g(x,y))=j(x,y)',
    'f(x,g(x,y))=g(x,f(x,y))',
    'f(x,g(y,f(y,z)))=f(x,g(y,f(x,f(y,z))))',
    'g(x,f(y,g(y,z)))=g(x,f(y,g(x,g(y,z))))',
    'f(g(x,y),j(x,y))=j(x,y)',
    'g(f(x,y),j(x,y))=j(x,y)',
    'f(c,a)=a', 'f(c,b)=b',
)


def parse(text):
    tokens = re.findall(r'[A-Za-z][A-Za-z0-9_]*|[(),]', text)
    assert ''.join(tokens) == ''.join(text.split())
    position = 0

    def term():
        nonlocal position
        symbol = tokens[position]
        position += 1
        if position < len(tokens) and tokens[position] == '(':
            position += 1
            left = term()
            assert tokens[position] == ','
            position += 1
            right = term()
            assert tokens[position] == ')'
            position += 1
            assert symbol in ('f', 'g', 'j')
            return symbol, left, right
        assert symbol in ('a', 'b', 'c') or VARIABLE.fullmatch(symbol)
        return symbol

    result = term()
    assert position == len(tokens)
    return result


def equation(text):
    parts = text.split('=')
    assert len(parts) == 2
    return tuple(map(parse, parts))


def is_variable(term):
    return isinstance(term, str) and term.startswith('?')


def rename(term, prefix):
    """Rename universally quantified variables apart; keep a,b,c fixed."""
    if isinstance(term, str):
        return '?' + prefix + term if VARIABLE.fullmatch(term) else term
    return term[0], *(rename(t, prefix) for t in term[1:])


def substitute(term, substitution):
    if is_variable(term) and term in substitution:
        return substitute(substitution[term], substitution)
    if isinstance(term, str):
        return term
    return term[0], *(substitute(t, substitution) for t in term[1:])


def occurs(variable, term):
    return (variable == term or isinstance(term, tuple)
            and any(occurs(variable, t) for t in term[1:]))


def unify(left, right, substitution):
    left, right = (substitute(t, substitution) for t in (left, right))
    if left == right:
        return
    if is_variable(right) and not is_variable(left):
        left, right = right, left
    if is_variable(left):
        assert not occurs(left, right)
        substitution[left] = right
        return
    assert isinstance(left, tuple) and isinstance(right, tuple)
    assert left[0] == right[0]
    for a, b in zip(left[1:], right[1:]):
        unify(a, b, substitution)


def match(pattern, target, substitution):
    """Verify that target is an instance; its variables stay frozen here."""
    if is_variable(pattern):
        if pattern not in substitution:
            substitution[pattern] = target
        assert substitution[pattern] == target
        return
    assert type(pattern) is type(target)
    if isinstance(pattern, str):
        assert pattern == target
        return
    assert pattern[0] == target[0]
    for a, b in zip(pattern[1:], target[1:]):
        match(a, b, substitution)


def at_path(term, path):
    for child in path:
        assert isinstance(term, tuple) and child in (1, 2)
        term = term[child]
    return term


def replace(term, path, replacement):
    if not path:
        return replacement
    assert isinstance(term, tuple) and path[0] in (1, 2)
    result = list(term)
    result[path[0]] = replace(result[path[0]], path[1:], replacement)
    return tuple(result)


def verify(certificate):
    steps = certificate['steps']
    actual = Counter(equation(eq) for _, eq, rule in steps if rule == ['axiom'])
    assert actual == Counter(map(equation, ASSUMPTIONS))
    proved = {}
    for identifier, text, rule in steps:
        assert isinstance(identifier, int) and identifier > 0 and identifier not in proved
        left, right = equation(text)
        if rule == ['axiom']:
            pass
        elif rule[0] == 'flip':
            assert len(rule) == 2
            source = proved[rule[1]]
            substitution = {}
            match(rename(source[1], 'flip'), left, substitution)
            match(rename(source[0], 'flip'), right, substitution)
        else:
            assert len(rule) == 5 and rule[0] == 'para'
            _, source_id, side, into_id, path = rule
            assert side in (1, 2) and path and path[0] in (1, 2)
            source = tuple(rename(t, 'source') for t in proved[source_id])
            into = tuple(rename(t, 'into') for t in proved[into_id])
            old, new = source[side - 1], source[2 - side]
            target_side, position = path[0] - 1, path[1:]
            old_target = at_path(into[target_side], position)
            substitution = {}
            unify(old, old_target, substitution)
            assert substitute(old, substitution) == substitute(old_target, substitution)
            output = list(into)
            output[target_side] = replace(output[target_side], position, new)
            output = [substitute(t, substitution) for t in output]
            instance = {}
            match(output[0], left, instance)
            match(output[1], right, instance)
        proved[identifier] = left, right
    assert proved[certificate['goal']] == equation('f(c,g(a,b))=g(a,b)')
    return Counter(rule[0] for _, _, rule in steps)


def check():
    path = Path(__file__).with_name('data') / 'core-choice-image-proof.json'
    certificate = json.loads(path.read_text())
    counts = verify(certificate)
    # Negative controls: accepting a different hypothesis or an unsupported
    # final equation would invalidate this as an equational certificate.
    for index in (0, len(certificate['steps']) - 1):
        altered = json.loads(path.read_text())
        altered['steps'][index][1] = 'f(c,g(a,b))=a'
        try:
            verify(altered)
        except AssertionError:
            pass
        else:
            raise AssertionError('accepted an altered certificate')

    images = quotients = 0
    for owners in range(3, 6):
        carrier = range(1, 1 << owners)

        def choice(i, x, y):
            return 1 << i if 1 << i in (x, y) else x | y

        for i, c in product(range(owners), carrier):
            image = {choice(i, c, x) for x in carrier}
            active = set()
            for x, y in product(image, repeat=2):
                assert x | y in image
                for j in range(owners):
                    value = choice(j, x, y)
                    assert value in image
                    if value != x | y:
                        active.add(j)
            assert len(active) <= 2 and len(active - {i}) <= 1
            for x in image:
                assert choice(i, c, x) == x
                value = c | x
                for j in range(owners):
                    value = choice(j, x, value)
                assert value == x
            images += 1
        for i, j, k in product(range(owners), repeat=3):
            if len({i, j, k}) != 3:
                continue
            image = {choice(i, 1 << j, x) for x in carrier}
            mapping = {x: (3 if x & (1 << k) else 0 if x == 1 << i
                           else 1 if x == 1 << j else 2) for x in image}
            assert set(mapping.values()) == {0, 1, 2, 3}
            for x, y in product(image, repeat=2):
                a, b = mapping[x], mapping[y]
                join = a if a == b else max(2, a, b)
                assert mapping[x | y] == join
                for owner in range(owners):
                    target = (0 if owner == i and 0 in (a, b)
                              else 1 if owner == j and 1 in (a, b) else join)
                    assert mapping[choice(owner, x, y)] == target
            quotients += 1
    print(f'Choice-image closure: {sum(counts.values())} universal equational '
          f'proof steps ({dict(counts)}); altered certificates rejected. '
          f'{images} native images have a reset unit and at most two active owners; '
          f'{quotients} maps onto two-owner generators checked.')


if __name__ == '__main__':
    check()
