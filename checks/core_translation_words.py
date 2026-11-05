"""Normal forms with many translations of one choice and one fixed other.

A positive token is a bit mask for a commuting product of F_i; zero is G.
The empty word is the identity. Consecutive internal F blocks are replaced
by cumulative unions of their masks, with repeated unions removed.
"""


def normalize(word):
    blocks = [0]
    for token in word:
        if token < 0:
            raise ValueError('translation tokens must be nonnegative')
        if token:
            blocks[-1] |= token
        else:
            blocks.append(0)
    if len(blocks) == 1:
        return (blocks[0],) if blocks[0] else ()
    result = [blocks[0], 0] if blocks[0] else [0]
    cumulative = 0
    for block in blocks[1:-1]:
        larger = cumulative | block
        if larger != cumulative:
            result.extend((larger, 0))
            cumulative = larger
    if blocks[-1]:
        result.append(blocks[-1])
    return tuple(result)
