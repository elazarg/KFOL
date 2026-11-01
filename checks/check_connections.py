"""Finite dependent-store model of open fragments and full strategies.

All legal stores, decision tables, cut positions, and profiles are enumerated
for a private dependent-vector protocol. This tests the connection interface,
not the metatheory of the paper's abstract data calculus.
"""

from dataclasses import dataclass, replace
from itertools import product


ALICE, BOB, BOTH = frozenset({0}), frozenset({1}), frozenset({0, 1})


@dataclass(frozen=True)
class Bind:
    name: str
    owner: int
    audience: frozenset
    dependencies: tuple
    support: tuple
    menu: object


@dataclass(frozen=True)
class Publish:
    name: str
    owner: int
    audience: frozenset


@dataclass(frozen=True)
class Interface:
    cells: tuple = ()
    pending: frozenset = frozenset()


def view(interface, store, owner):
    return tuple((cell.name, value) for cell, value in zip(interface.cells, store)
                 if owner in cell.audience)


def advance(interface, command):
    names = [cell.name for cell in interface.cells]
    if isinstance(command, Bind):
        assert command.name not in names and command.owner in command.audience
        local = {cell.name for cell in interface.cells if command.owner in cell.audience}
        assert set(command.dependencies) <= set(command.support) <= local
        for cell in interface.cells:
            if cell.name in command.support:
                assert set(cell.dependencies) <= set(command.support)
        for role in command.audience:
            assert set(command.dependencies) <= {
                cell.name for cell in interface.cells if role in cell.audience}
        return Interface(interface.cells + (command,), interface.pending | {command.name})
    assert command.name in interface.pending
    index = names.index(command.name)
    old = interface.cells[index]
    assert old.owner == command.owner and old.audience <= command.audience
    for role in command.audience - old.audience:
        assert set(old.dependencies) <= {
            cell.name for cell in interface.cells[:index] if role in cell.audience}
    cells = list(interface.cells)
    cells[index] = replace(old, audience=command.audience)
    return Interface(tuple(cells), interface.pending - {command.name})


def options(command, interface, store):
    env = {cell.name: value for cell, value in zip(interface.cells, store)
           if cell.name in command.dependencies}
    return command.menu(env)


def analyze(commands, interface, worlds, offset=0):
    domains = {}
    for stage, command in enumerate(commands, offset):
        following = advance(interface, command)
        if isinstance(command, Bind):
            new_worlds = set()
            for store in worlds:
                key = (command.owner, stage, view(interface, store, command.owner))
                menu = options(command, interface, store)
                assert domains.setdefault(key, menu) == menu
                new_worlds.update(store + (value,) for value in menu)
            worlds = frozenset(new_worlds)
        interface = following
    return interface, worlds, domains


def run(commands, interface, store, profile, offset=0):
    for stage, command in enumerate(commands, offset):
        following = advance(interface, command)
        if isinstance(command, Bind):
            key = (command.owner, stage, view(interface, store, command.owner))
            value = profile[key]
            assert value in options(command, interface, store)
            store += (value,)
        interface = following
    return interface, store


def sealing(commands, marked, observer=1):
    marked = set(marked)
    for command in commands:
        if isinstance(command, Bind):
            if marked.intersection(command.support):
                marked.add(command.name)
                if observer in command.audience:
                    return None
        elif command.name in marked and observer in command.audience:
            return None
    return frozenset(marked)


def check():
    commands = (
        Bind('n', 0, ALICE, (), (), lambda _: (1, 2)),
        Bind('v', 0, ALICE, ('n',), ('n',),
             lambda env: tuple(product((False, True), repeat=env['n']))),
        Bind('b', 1, BOB, (), (), lambda _: (False, True)),
        Publish('n', 0, BOTH), Publish('v', 0, BOTH), Publish('b', 1, BOTH),
    )
    initial, worlds = Interface(), frozenset({()})
    final, possible, domains = analyze(commands, initial, worlds)
    assert not final.pending and len(possible) == 12
    assert len(domains) == 4  # Alice's n, both vector indices, Bob's hidden choice.
    assert len([key for key in domains if key[0] == 1]) == 1
    profiles = [dict(zip(domains, values)) for values in product(*domains.values())]
    assert len(profiles) == 32

    cuts = [analyze(commands[:cut], initial, worlds) for cut in range(len(commands) + 1)]
    for cut, (boundary, all_stores, before_domains) in enumerate(cuts):
        after, suffix_stores, after_domains = analyze(commands[cut:], boundary, all_stores, cut)
        assert after == final and suffix_stores == possible
        assert not before_domains.keys() & after_domains.keys()
        assert before_domains | after_domains == domains
        for profile in profiles:
            prefix_profile = {key: profile[key] for key in before_domains}
            suffix_profile = {key: profile[key] for key in after_domains}
            _, store = run(commands[:cut], initial, (), prefix_profile)
            assert store in all_stores
            assert run(commands[cut:], boundary, store, suffix_profile, cut) == run(
                commands, initial, (), profile)
    # Deviations are all decision tables of a role, not just reached entries.
    for role in (0, 1):
        own_keys = [key for key in domains if key[0] == role]
        for cut, (_, _, before_domains) in enumerate(cuts):
            first = [key for key in own_keys if key in before_domains]
            second = [key for key in own_keys if key not in before_domains]
            joined = {tuple(dict(zip(first + second, a + b))[key] for key in own_keys)
                      for a in product(*(domains[key] for key in first))
                      for b in product(*(domains[key] for key in second))}
            assert joined == set(product(*(domains[key] for key in own_keys)))

    for first in range(len(commands) + 1):
        for second in range(first, len(commands) + 1):
            left_phase, left_worlds, _ = cuts[first]
            middle, middle_worlds, _ = analyze(commands[first:second], left_phase,
                                              left_worlds, first)
            assert (middle, middle_worlds) == cuts[second][:2]
            for profile in profiles:
                phase, store = run(commands[:first], initial, (), profile)
                phase, store = run(commands[first:second], phase, store, profile, first)
                assert run(commands[second:], phase, store, profile, second) == run(
                    commands, initial, (), profile)

    # Selecting the actual prefix store would erase off-path vector decisions.
    boundary, all_stores, _ = cuts[1]
    _, _, all_suffix = analyze(commands[1:], boundary, all_stores, 1)
    _, _, pruned_suffix = analyze(commands[1:], boundary, frozenset({(1,)}), 1)
    assert len(all_suffix) == 3 and len(pruned_suffix) == 2
    assert all(len(store[1]) == store[0] for store in possible)
    try:
        analyze((commands[4],), cuts[2][0], cuts[2][1])
    except AssertionError:
        pass
    else:
        raise AssertionError('Published the vector before its index')

    continuations = (commands[1:3], commands[1:4], (
        Bind('copy', 0, ALICE, (), ('n',), lambda _: (False, True)),
        Publish('copy', 0, BOTH)))
    for continuation in continuations:
        expected = sealing(continuation, {'n'})
        for cut in range(len(continuation) + 1):
            marks = sealing(continuation[:cut], {'n'})
            actual = None if marks is None else sealing(continuation[cut:], marks)
            assert actual == expected
    assert sealing(continuations[0], {'n'}) == frozenset({'n', 'v'})
    assert sealing(continuations[1], {'n'}) is None
    assert sealing(continuations[2], {'n'}) is None
    print('Private connection: all 32 full profiles, 7 cuts, 28 three-way splits; '
          'dependent witnesses, all deviations, hidden views, pending cells, and '
          'composed sealing checks passed.')


if __name__ == '__main__':
    check()
