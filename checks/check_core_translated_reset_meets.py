"""Audit join preservation of every nonempty partial reset meet.

The uniform proof uses commuting complementary contractions on a shifted
interval. Principal-ideal bitsets below verify the full greatest-lower-
bound assertion, rather than just inequalities at the displayed value.
"""

from check_core_owned_reset import test_models
from core_basis import MIXED_JOIN, MIXED_OPERATIONS


def audit(add, operations):
    n = len(add)
    ideals = [sum(1 << x for x in range(n) if add[x][y] == y)
              for y in range(n)]
    subsets = [tuple(i for i in range(len(operations)) if mask >> i & 1)
               for mask in range(1, 1 << len(operations))]
    checks = stages = 0
    for x in range(n):
        for u in range(n):
            if add[x][u] != u:
                continue
            for selected in subsets:
                q = u
                for i in selected:
                    q = operations[i][x][q]
                lower = (1 << n) - 1
                for i in selected:
                    lower &= ideals[operations[i][x][u]]
                assert lower == ideals[q]
                for z in range(n):
                    value = add[z][q]
                    shifted = add[z][u]
                    lower = (1 << n) - 1
                    for i in selected:
                        shifted = add[z][operations[i][x][shifted]]
                        lower &= ideals[add[z][operations[i][x][u]]]
                        stages += 1
                    assert shifted == value
                    assert lower == ideals[value]
                    checks += 1
    return checks, stages


def check():
    models = test_models() + [(MIXED_JOIN, MIXED_OPERATIONS)]
    results = [audit(add, ops) for add, ops in models]
    checks = sum(x for x, _ in results)
    stages = sum(x for _, x in results)
    print(f'Translated reset meets: {checks} full lower-bound checks and '
          f'{stages} shifted-fold stages in {len(models)} models. '
          'Every nonempty owner subset and every join translation is '
          'included. The written proof needs only Gamma_K.')


if __name__ == '__main__':
    check()
