"""Finite countermodels for the K-FOG manuscript assessment.

Run: python3 research/finite_audit.py

This is exhaustive finite experimentation, not a proof-assistant formalization.
Moves have Boolean domains and explicit observation keys. Every local policy is
a total truth table, including off-path observations. A role's strategy contains
all of its local policies; unilateral deviations replace the whole strategy.
"""

from dataclasses import dataclass
from itertools import product
from typing import Callable

Bits = tuple[int, ...]
Policy = Bits
Strategy = tuple[Policy, ...]
Profile = tuple[Strategy, ...]


@dataclass(frozen=True)
class Move:
    owner: int
    visible: tuple[int, ...] = ()


class Game:
    def __init__(self, players: int, moves: tuple[Move, ...], payoff: Callable):
        self.players = players
        self.moves = moves
        self.payoff = payoff
        self.positions = tuple(
            tuple(m for m, move in enumerate(moves) if move.owner == i)
            for i in range(players)
        )
        for m, move in enumerate(moves):
            assert 0 <= move.owner < players
            assert len(set(move.visible)) == len(move.visible)
            assert all(0 <= v < m for v in move.visible)
        self.strategies = tuple(
            tuple(product(*(
                tuple(product((0, 1), repeat=2 ** len(moves[m].visible)))
                for m in positions
            )))
            for positions in self.positions
        )

    def profiles(self):
        return product(*self.strategies)

    def play(self, profile: Profile) -> Bits:
        counters = [0] * self.players
        history = []
        for move in self.moves:
            index = 0
            for v in move.visible:
                index = 2 * index + history[v]
            policy = profile[move.owner][counters[move.owner]]
            history.append(policy[index])
            counters[move.owner] += 1
        return tuple(history)

    def outcome(self, profile: Profile) -> Bits:
        return tuple(map(int, self.payoff(self.play(profile))))

    def force(self, coalition: tuple[int, ...], goals=None) -> bool:
        if goals is None:
            goals = coalition
        outsiders = tuple(i for i in range(self.players) if i not in coalition)
        for own in product(*(self.strategies[i] for i in coalition)):
            profile = [None] * self.players
            for i, strategy in zip(coalition, own):
                profile[i] = strategy
            wins = True
            for other in product(*(self.strategies[i] for i in outsiders)):
                for i, strategy in zip(outsiders, other):
                    profile[i] = strategy
                if not all(self.outcome(tuple(profile))[i] for i in goals):
                    wins = False
                    break
            if wins:
                return True
        return False

    def forces(self) -> Bits:
        return tuple(int(self.force((i,))) for i in range(self.players))

    def is_ne(self, profile: Profile) -> bool:
        current = self.outcome(profile)
        for i in range(self.players):
            for strategy in self.strategies[i]:
                deviated = profile[:i] + (strategy,) + profile[i + 1:]
                if self.outcome(deviated)[i] > current[i]:
                    return False
        return True

    def perfect_recall(self, role: int) -> bool:
        remembered = set()
        for m in self.positions[role]:
            visible = set(self.moves[m].visible)
            if not remembered <= visible:
                return False
            remembered |= visible | {m}
        return True


def qbf(game: Game, role: int, prefix: Bits = ()) -> bool:
    """Naive ordinary-FO projection; sound only in the broadcast fragment."""
    m = len(prefix)
    if m == len(game.moves):
        return bool(game.payoff(prefix)[role])
    branches = (qbf(game, role, prefix + (a,)) for a in (0, 1))
    return any(branches) if game.moves[m].owner == role else all(branches)


def run():
    # DQBF: forall y; x1(y), x2(); (x1=y and x2=y) is false.
    goal = lambda h: (h[1] == h[0] and h[2] == h[0], 0)
    manuscript = Game(2, (Move(1), Move(0, (0,)), Move(0, (1,))), goal)
    repaired = Game(2, (Move(1), Move(0, (0,)), Move(0)), goal)
    assert manuscript.force((0,))
    assert not repaired.force((0,))
    assert not manuscript.perfect_recall(0)
    assert not repaired.perfect_recall(0)
    print("DQBF countermodel: manuscript encoding wins; correct dependency encoding loses.")

    matching = Game(2, (Move(1), Move(0)), lambda h: (h[0] == h[1], h[0] != h[1]))
    assert matching.forces() == (0, 0)
    assert qbf(matching, 0)
    print("Hidden matching pennies: forceability (0, 0); naive FO projection for role 0 true.")

    cooperative = Game(2, (Move(0),), lambda h: (h[0] == 0,) * 2)
    complemented = Game(2, cooperative.moves, lambda h: (h[0] != 0,) * 2)
    assert cooperative.forces() == (1, 0)
    assert complemented.forces() == (1, 0)
    assert cooperative.force((0, 1))
    print("Equal goals: individual forceability differs by role; complement does not negate it.")

    # Same individual forceability; distinct coalition ability, already with broadcast.
    moves = (Move(0), Move(1, (0,)))
    aligned = Game(3, moves, lambda h: (h == (0, 0), h == (0, 0), 0))
    conflicting = Game(3, moves, lambda h: (h == (0, 0), h == (1, 1), 0))
    assert aligned.forces() == conflicting.forces() == (0, 0, 0)
    assert aligned.force((0, 1)) and not conflicting.force((0, 1))
    print("Individual projections lose coalition information: (0, 0, 0) in both examples.")

    # A variable absent from all terminal formulas can still signal to a policy.
    talk = Game(2, (Move(0), Move(1, (0,))), lambda h: (h[1] == 0, 1))
    before = (((0,),), ((0, 1),))
    after = (((1,),), ((0, 1),))
    assert talk.outcome(before) == (1, 1) and talk.outcome(after) == (0, 1)
    print("Cheap-talk quotient: changing only terminal-unused c can change the outcome.")

    # An irrelevant occurrence of role 1 cannot justify replacing that whole role.
    slicing = Game(2, (Move(1), Move(1, (0,))), lambda h: (h[0] == 0, 1))
    before = ((), ((0,), (0, 0)))
    after = ((), ((1,), (0, 0)))
    assert slicing.outcome(before)[0] != slicing.outcome(after)[0]
    print("Slicing countermodel: final unused move is irrelevant; its owner's full strategy is not.")

    # Check every two-role Boolean payoff table in both observation regimes.
    games_checked = profiles_checked = projection_checks = 0
    histories = tuple(product((0, 1), repeat=2))
    for visible in ((), (0,)):
        for table in product((0, 1), repeat=8):
            values = {h: table[2 * n:2 * n + 2] for n, h in enumerate(histories)}
            game = Game(2, (Move(0), Move(1, visible)), values.__getitem__)
            forces = game.forces()
            for profile in game.profiles():
                if game.is_ne(profile):
                    assert all(game.outcome(profile)[i] >= forces[i] for i in range(2))
                profiles_checked += 1
            if all(forces):
                assert any(all(game.outcome(p)) for p in game.profiles())
            if visible:
                assert forces == tuple(int(qbf(game, i)) for i in range(2))
                projection_checks += 2
            games_checked += 1
    print(f"Exhaustive checks: {games_checked} games, {profiles_checked} profiles, "
          f"{projection_checks} broadcast projection comparisons.")
    print("All finite checks passed. General results still require formal proofs.")


if __name__ == "__main__":
    run()
