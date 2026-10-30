"""Independent finite checks of interaction, SPE, and disclosure.

These check the explicit Python models below, not the metatheory of D.
SPE is checked by enumerating full unilateral deviations in every subgame,
independently of the recursive winner-set operation used for comparison.
"""

from dataclasses import dataclass, replace
from itertools import permutations, product

from check_protocols import Script, reduce_policy, run_tables, reachable


SUBTREE = ((0, 1, 2), (1,), (2,))


def leaf_index(profile, node=0):
    if node == 0:
        branch = profile[0]
        return 2 * branch + profile[1 + branch]
    return 2 * (node - 1) + profile[node]


def nash_at(profile, owners, payoffs, node=0):
    current = payoffs[leaf_index(profile, node)]
    for role in set(owners[n] for n in SUBTREE[node]):
        controlled = tuple(n for n in SUBTREE[node] if owners[n] == role)
        for actions in product((0, 1), repeat=len(controlled)):
            deviation = list(profile)
            for occurrence, action in zip(controlled, actions):
                deviation[occurrence] = action
            if payoffs[leaf_index(deviation, node)][role] > current[role]:
                return False
    return True


def subgame_perfect(profile, owners, payoffs):
    return all(nash_at(profile, owners, payoffs, node) for node in range(3))


def choice(role, left, right):
    return frozenset((role,)) if left == {role} or right == {role} else left | right


def rational_check():
    games = profiles = 0
    for owners in product(range(3), repeat=3):
        for winners in product(range(3), repeat=4):
            payoffs = tuple(tuple(int(w == i) for i in range(3)) for w in winners)
            actual = set()
            for profile in product((0, 1), repeat=3):
                if subgame_perfect(profile, owners, payoffs):
                    actual.add(winners[leaf_index(profile)])
                profiles += 1
            expected = choice(
                owners[0],
                choice(owners[1], frozenset((winners[0],)), frozenset((winners[1],))),
                choice(owners[2], frozenset((winners[2],)), frozenset((winners[3],))),
            )
            assert actual and actual == expected
            games += 1
    for count in (2, 3, 4):
        values = {frozenset((i,)) for i in range(count)}
        while True:
            expanded = values | {
                choice(i, left, right)
                for i in range(count) for left in values for right in values
            }
            if expanded == values:
                break
            values = expanded
        assert len(values) == (2 if count == 2 else 2**count - 1)
        for i in range(count):
            for a, b, c in product(values, repeat=3):
                assert choice(i, a, choice(i, b, c)) == choice(i, choice(i, a, b), c)
                assert choice(i, a, b) == choice(i, b, a)
                assert choice(i, a, a) == a
    atoms = [frozenset((i,)) for i in range(3)]
    a, b, c = atoms
    assert choice(1, choice(0, a, b), c) == {0, 2}
    assert choice(0, choice(1, a, c), choice(1, b, c)) == {0, 1, 2}
    values = [frozenset(i for i in range(3) if mask & (1 << i)) for mask in range(1, 8)]
    for permutation in permutations(range(3)):
        rename = lambda s: frozenset(permutation[i] for i in s)
        for role, left, right in product(range(3), values, values):
            assert rename(choice(role, left, right)) == choice(
                permutation[role], rename(left), rename(right)
            )
    print(f"Rational analysis: {games} games, {profiles} full profiles, and finite algebra laws passed.")


def strategy_check():
    # Same actual trace, different Nash status.
    owners = (0, 1, 1)
    payoffs = ((1, 1), (1, 1), (0, 0), (2, 1))
    assert nash_at((0, 0, 0), owners, payoffs)
    assert not nash_at((0, 0, 1), owners, payoffs)
    assert leaf_index((0, 0, 0)) == leaf_index((0, 0, 1))

    # Same reduced plans, different subgame-perfect status.
    owners = (0, 0, 0)
    payoffs = ((1, 0), (1, 0), (0, 1), (1, 0))
    assert not subgame_perfect((0, 0, 0), owners, payoffs)
    assert subgame_perfect((0, 0, 1), owners, payoffs)
    assert nash_at((0, 0, 0), owners, payoffs)
    assert nash_at((0, 0, 1), owners, payoffs)
    script = Script((0, 0), (lambda _: (0, 1),) * 2, (lambda _: None,) * 2)
    first = ({(): 0}, {(0,): 0, (1,): 0})
    second = ({(): 0}, {(0,): 0, (1,): 1})
    assert run_tables(script, first) == run_tables(script, second)
    for role in range(2):
        assert reduce_policy(script, first, role) == reduce_policy(script, second, role)
    print("Strategies: execution/Nash and reduced-plan/SPE counterexamples passed.")


@dataclass(frozen=True)
class DataType:
    name: str
    dependencies: tuple
    accepts: object


BOOL = DataType("Bool", (), lambda _, value: type(value) is bool)
POSITIVE = DataType("Positive", (), lambda _, value: type(value) is int and value > 0)
VECTOR = DataType(
    "Vec(Bool,n)", ("n",),
    lambda store, value: isinstance(value, tuple)
    and len(value) == store["n"] and all(type(v) is bool for v in value),
)


@dataclass(frozen=True)
class Bind:
    name: str
    owner: int
    audience: frozenset
    data_type: DataType
    support: tuple
    implementation: object


@dataclass(frozen=True)
class Publish:
    name: str
    owner: int
    audience: frozenset


@dataclass(frozen=True)
class Cell:
    owner: int
    audience: frozenset
    data_type: DataType


def require(condition):
    if not condition:
        raise ValueError("Ill-formed phase or implementation")


def phase_run(commands, complete=False):
    cells, store, pending = {}, {}, set()
    states = []

    def visible(role, before=None):
        names = list(cells)
        if before is not None:
            names = names[:names.index(before)]
        return {name for name in names if role in cells[name].audience}

    def snapshot(stage):
        views = tuple(
            (stage, tuple((name, store[name]) for name in cells if role in cells[name].audience))
            for role in range(3)
        )
        states.append((dict(store), views))

    snapshot(0)
    for stage, command in enumerate(commands, 1):
        previous = dict(store)
        if isinstance(command, Bind):
            require(command.name not in cells and command.owner in command.audience)
            support = set(command.support)
            require(support <= visible(command.owner))
            require(set(command.data_type.dependencies) <= support)
            for dependency in support:
                require(set(cells[dependency].data_type.dependencies) <= support)
            for role in command.audience:
                require(set(command.data_type.dependencies) <= visible(role))
            arguments = {name: store[name] for name in command.support}
            value = command.implementation(arguments)
            require(command.data_type.accepts(store, value))
            cells[command.name] = Cell(command.owner, command.audience, command.data_type)
            store[command.name] = value
            pending.add(command.name)
        else:
            require(command.name in pending)
            cell = cells[command.name]
            require(command.owner == cell.owner and cell.audience <= command.audience)
            for role in command.audience - cell.audience:
                require(set(cell.data_type.dependencies) <= visible(role, before=command.name))
            cells[command.name] = replace(cell, audience=command.audience)
            pending.remove(command.name)
        assert all(store[name] == value for name, value in previous.items())
        snapshot(stage)
    require(not complete or not pending)
    return states


def sealed(commands, protected="c", observer=1):
    marked = set()
    for command in commands:
        if isinstance(command, Bind):
            if command.name == protected or marked.intersection(command.support):
                marked.add(command.name)
                if observer in command.audience:
                    return False
        elif command.name in marked and observer in command.audience:
            return False
    return protected in marked


ALICE = frozenset((0,))
BOB = frozenset((1,))
BOTH = frozenset((0, 1))
ALL = frozenset((0, 1, 2))


def boolean_cell(name, kind, dependency):
    if kind < 2:
        return Bind(name, 0, ALICE, BOOL, (), lambda _: bool(kind))
    return Bind(
        name, 0, ALICE, BOOL, (dependency,),
        lambda env: env[dependency] if kind == 2 else not env[dependency],
    )


def hiding_check():
    accepted = total = 0
    for d_kind, e_kind, publication in product(range(4), range(4), (None, "c", "d", "e")):
        executions, programs = [], []
        for secret in (False, True):
            program = [
                Bind("c", 0, ALICE, BOOL, (), lambda _, value=secret: value),
                boolean_cell("d", d_kind, "c"),
                boolean_cell("e", e_kind, "d"),
            ]
            if publication:
                program.append(Publish(publication, 0, BOTH))
            programs.append(program)
            executions.append(phase_run(program))
        total += 1
        if sealed(programs[0]):
            for left, right in zip(*executions):
                assert left[1][1] == right[1][1]
            accepted += 1
    assert total == 64 and accepted == 36

    # An indirect opening leaks before Pub(c); audiences alone do not suffice.
    copy_runs = []
    for secret in (False, True):
        program = [
            Bind("c", 0, ALICE, BOOL, (), lambda _, value=secret: value),
            boolean_cell("d", 2, "c"),
            Publish("d", 0, BOTH),
        ]
        assert not sealed(program)
        copy_runs.append(phase_run(program))
    assert copy_runs[0][-1][1][1] != copy_runs[1][-1][1][1]

    # Bob fixes the same payload for both hidden Alice values.
    for bob_choice in (False, True):
        for alice_choice in (False, True):
            program = [
                Bind("c", 0, ALICE, BOOL, (), lambda _: alice_choice),
                Bind("d", 1, BOB, BOOL, (), lambda _: bob_choice),
                Publish("c", 0, ALL), Publish("d", 1, ALL),
            ]
            states = phase_run(program, complete=True)
            assert states[2][0]["d"] == bob_choice
            assert states[-1][0]["c"] == alice_choice
    print(f"Disclosure: {total} finite prefixes, {accepted} sealing certificates, and indirect-leak checks passed.")


def dependent_phase_check():
    prefixes = []
    for number in (1, 2):
        program = [
            Bind("n", 0, ALICE, POSITIVE, (), lambda _: number),
            Bind("v", 0, ALICE, VECTOR, ("n",), lambda env: (True,) * env["n"]),
            Bind("b", 1, BOB, BOOL, (), lambda _: False),
            Publish("n", 0, ALL), Publish("v", 0, ALL), Publish("b", 1, ALL),
        ]
        states = phase_run(program, complete=True)
        assert sealed(program[:3], protected="n")
        prefixes.append(states[:4])
        assert states[-1][0]["v"] == (True,) * number
        invalid = program[:3] + [Publish("v", 0, ALL)]
        try:
            phase_run(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("Published an indexed type before its index became available")
    assert all(left[1][1] == right[1][1] for left, right in zip(*prefixes))
    print("Dependent phases: stable private vector indices and rejection of premature publication passed.")


def knowledge_iff_check():
    worlds = (0, 1, 2)
    observations = tuple(product(range(3), repeat=3))
    cases = 0
    for first, second in product(observations, repeat=2):
        views = (lambda h: first[h], lambda h: second[h])
        for readout in product((0, 1), repeat=3):
            invariant = all(
                observe(x) != observe(y) or readout[x] == readout[y]
                for observe in views for x, y in product(worlds, repeat=2)
            )
            common_everywhere = all(
                all(readout[h] == readout[start] for h in reachable(worlds, views, start))
                for start in worlds
            )
            assert invariant == common_everywhere
            cases += 1
    print(f"Knowledge: both directions of the readout characterization passed in {cases} finite cases.")


if __name__ == "__main__":
    strategy_check()
    rational_check()
    hiding_check()
    dependent_phase_check()
    knowledge_iff_check()
